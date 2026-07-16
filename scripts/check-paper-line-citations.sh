#!/usr/bin/env bash
# Copyright (c) 2026 Adam Benenson. All rights reserved.
# Released under Apache 2.0 OR MIT license as described in the file LICENSE.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

perl -Mstrict -Mwarnings - "$ROOT" <<'PERL'
use File::Find;

my ($root) = @ARGV;

my %source_cache;
my %lean_decl_index;
my $lean_decl_index_loaded = 0;
my $failures = 0;
my $checked = 0;
my $checked_bare = 0;
my $whitelisted_strict = 0;
my $whitelisted_bare = 0;

my %strict_citation_paragraph_whitelist = ();

my %bare_line_reference_whitelist = ();

sub relative_path {
  my ($path) = @_;
  $path =~ s/^\Q$root\E\///;
  return $path;
}

sub read_lines {
  my ($path) = @_;
  return $source_cache{$path} if exists $source_cache{$path};
  open my $fh, "<", $path or die "cannot read $path: $!";
  my @lines = <$fh>;
  close $fh;
  $source_cache{$path} = \@lines;
  return \@lines;
}

sub declaration_name {
  my ($line) = @_;
  if ($line =~ /^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+|partial\s+|unsafe\s+)*(?:def|theorem|lemma|structure|class|inductive|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b/) {
    my $name = $1;
    $name =~ s/^.*\.//;
    return $name;
  }
  return undef;
}

sub load_lean_decl_index {
  return if $lean_decl_index_loaded;
  $lean_decl_index_loaded = 1;

  find(
    {
      wanted => sub {
        my $path = $File::Find::name;
        return if $path !~ /\.lean\z/;
        return if $path =~ m{/(?:\.lake|lake-packages)/};

        my $lines = read_lines($path);
        (my $rel = $path) =~ s/^\Q$root\E\///;
        for my $i (0 .. $#$lines) {
          my $name = declaration_name($lines->[$i]);
          next if !defined $name;
          push @{$lean_decl_index{$name}}, {
            rel => $rel,
            path => $path,
            line => $i + 1,
          };
        }
      },
      no_chdir => 1,
    },
    "$root/lean/Legitimacy"
  );
}

sub active_declaration_at {
  my ($lines, $line_number) = @_;
  for (my $i = $line_number - 1; $i >= 0; --$i) {
    my $name = declaration_name($lines->[$i]);
    return ($name, $i + 1) if defined $name;
  }
  return (undef, undef);
}

sub doc_comment_declaration_at {
  my ($lines, $line_number) = @_;
  return (undef, undef) if $line_number < 1 || $line_number > scalar(@$lines);

  my $start = $line_number - 1;
  while ($start >= 0 && $lines->[$start] !~ m{/\--}) {
    --$start;
  }
  return (undef, undef) if $start < 0;

  my $end = $start;
  while ($end <= $#$lines && $lines->[$end] !~ m{-/}) {
    ++$end;
  }
  return (undef, undef) if $end > $#$lines;
  return (undef, undef) if $line_number - 1 > $end;

  for (my $i = $end + 1; $i <= $#$lines; ++$i) {
    next if $lines->[$i] =~ /^\s*$/;
    my $name = declaration_name($lines->[$i]);
    return ($name, $i + 1) if defined $name;
    return (undef, undef);
  }
  return (undef, undef);
}

sub cited_declaration_at {
  my ($lines, $line_number) = @_;
  my $exact_name = declaration_name($lines->[$line_number - 1]);
  return ($exact_name, $line_number, 1) if defined $exact_name;

  my ($doc_name, $doc_line) = doc_comment_declaration_at($lines, $line_number);
  return ($doc_name, $doc_line, 0) if defined $doc_name;

  my ($active_name, $active_line) = active_declaration_at($lines, $line_number);
  return ($active_name, $active_line, 0);
}

sub symbols_in_text {
  my ($text) = @_;
  my %symbols;
  while ($text =~ /`([^`\n]+)`/g) {
    my $code = $1;
    next if $code =~ m{(?:^|/)lean/|\.lean:[0-9]+};
    while ($code =~ /([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)/g) {
      my $symbol = $1;
      $symbol =~ s/^.*\.//;
      $symbols{$symbol} = 1;
    }
  }
  return \%symbols;
}

sub paragraph_symbols {
  my ($paragraph) = @_;
  return symbols_in_text($paragraph);
}

sub sentence_containing_offset {
  my ($paragraph, $offset) = @_;
  my $start = 0;
  while ($paragraph =~ /\.[[:space:]]+/g) {
    last if $-[0] >= $offset;
    $start = pos($paragraph);
  }

  my $tail = substr($paragraph, $offset);
  my $end = length($paragraph);
  if ($tail =~ /\.[[:space:]]+/) {
    $end = $offset + $+[0];
  }

  return substr($paragraph, $start, $end - $start);
}

sub offset_line_number {
  my ($content, $offset) = @_;
  my $prefix = substr($content, 0, $offset);
  return 1 + ($prefix =~ tr/\n//);
}

sub validate_bare_line_reference {
  my ($paper_path, $paper_line, $paragraph, $offset, $line_number) = @_;
  load_lean_decl_index();

  my $paper_rel = relative_path($paper_path);
  if (exists $bare_line_reference_whitelist{"$paper_rel:$paper_line:$line_number"}) {
    ++$whitelisted_bare;
    return;
  }

  my $sentence = sentence_containing_offset($paragraph, $offset);
  my $symbols = symbols_in_text($sentence);
  if (!%$symbols) {
    $symbols = paragraph_symbols($paragraph);
  }

  my @symbols = grep { exists $lean_decl_index{$_} } sort keys %$symbols;
  return if !@symbols;

  ++$checked_bare;
  for my $symbol (@symbols) {
    for my $decl (@{$lean_decl_index{$symbol}}) {
      my $lines = read_lines($decl->{path});
      next if $line_number < 1 || $line_number > scalar(@$lines);
      my $target_line = $lines->[$line_number - 1];
      return if $target_line =~ /^\s*instance\b/ && $target_line =~ /\b\Q$symbol\E\b/;
      my ($active_name, undef) = active_declaration_at($lines, $line_number);
      return if defined($active_name) && $active_name eq $symbol;
    }
  }

  my @expected;
  for my $symbol (@symbols) {
    for my $decl (@{$lean_decl_index{$symbol}}) {
      push @expected, "`$symbol` at $decl->{rel}:$decl->{line}";
    }
  }
  @expected = @expected[0 .. 4] if @expected > 5;
  warn "$paper_path:$paper_line: bare line reference line $line_number "
    . "does not resolve to the nearby Lean symbol(s); expected "
    . join("; ", @expected) . "\n";
  ++$failures;
}

my @paper_paths = sort glob("$root/papers/*.md");
for my $paper_path (@paper_paths) {
  my $paper_rel = relative_path($paper_path);
  open my $pfh, "<", $paper_path or die "cannot read $paper_path: $!";
  my $content = do {
    local $/;
    <$pfh>;
  };
  close $pfh;

  my @lines = split /\n/, $content, -1;
  for my $i (0 .. $#lines) {
    if ($lines[$i] =~ /\.lean:\d+/) {
      warn "$paper_path:" . ($i + 1)
        . ": file:line citations forbidden in paper prose; "
        . "use identifier + module-path convention; "
        . "verification anchor tag is the durability mechanism\n";
      ++$failures;
    }
  }

  my $cursor = 0;
  while ($content =~ /(\S(?:.*?(?:\n(?!\s*\n).*?)*)?)(?:\n\s*\n|\z)/sg) {
    my $paragraph = $1;
    my $paragraph_start = $-[1];
    next if !defined $paragraph || $paragraph !~ /\S/;

    my $symbols = paragraph_symbols($paragraph);
    while ($paragraph =~ /(lean\/(?:Legitimacy|\.lake\/packages)\/[A-Za-z0-9_\/.-]+\.lean):([0-9]+)/g) {
      my ($rel, $line_number) = ($1, int($2));
      my $cite_offset = $-[0];
      my $paper_line = offset_line_number($content, $paragraph_start + $-[0]);
      my $source_path = "$root/$rel";
      ++$checked;

      if (!-f $source_path) {
        warn "$paper_path:$paper_line: cited Lean file does not exist: $rel\n";
        ++$failures;
        next;
      }

      my $lines = read_lines($source_path);
      if ($line_number < 1 || $line_number > scalar(@$lines)) {
        warn "$paper_path:$paper_line: cited line out of range: $rel:$line_number\n";
        ++$failures;
        next;
      }

      my ($name, $active_line, $exact_anchor) =
        cited_declaration_at($lines, $line_number);

      if (!defined $name) {
        warn "$paper_path:$paper_line: no Lean declaration anchors $rel:$line_number\n";
        ++$failures;
        next;
      }

      my $strict_symbols = 1;
      my $local_symbols = symbols_in_text(
        sentence_containing_offset($paragraph, $cite_offset));
      if (!%$local_symbols) {
        $local_symbols = $symbols;
      }
      if ($strict_symbols && !$local_symbols->{$name}) {
        if (exists $strict_citation_paragraph_whitelist{"$paper_rel:$paper_line"}) {
          ++$whitelisted_strict;
          next;
        }
        my @near = sort keys %$local_symbols;
        warn "$paper_path:$paper_line: $rel:$line_number resolves to '$name' "
          . "(declaration line $active_line), but cite context does not name it; "
          . "local symbols: " . (@near ? join(", ", @near) : "(none)") . "\n";
        ++$failures;
        next;
      }

      if (!$exact_anchor && $active_line == $line_number) {
        warn "$paper_path:$paper_line: internal error resolving $rel:$line_number\n";
        ++$failures;
        next;
      }
    }

    while ($paragraph =~ /\bline\s+([0-9]+)\b/g) {
      my $paper_line = offset_line_number($content, $paragraph_start + $-[0]);
      validate_bare_line_reference(
        $paper_path,
        $paper_line,
        $paragraph,
        $-[0],
        int($1)
      );
    }
  }
}

if ($failures) {
  die "paper Lean line citation check failed with $failures failure(s)\n";
}

print "paper Lean line citations: OK ($checked citations checked";
print ", $checked_bare bare line references checked" if $checked_bare;
print ", $whitelisted_strict strict cite whitelist hits" if $whitelisted_strict;
print ", $whitelisted_bare bare line whitelist hits" if $whitelisted_bare;
print ")\n";
PERL
