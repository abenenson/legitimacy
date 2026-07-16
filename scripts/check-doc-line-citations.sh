#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"

perl -Mstrict -Mwarnings - "$ROOT" <<'PERL'
use File::Find;

my ($root) = @ARGV;
my @doc_paths = (
  "$root/docs/repository-context.md",
  "$root/FRAMEWORK-LIMITS.md",
);

my %source_cache;
my %lean_anchor_index;
my $failures = 0;
my $checked = 0;

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

sub field_name {
  my ($line) = @_;
  if ($line =~ /^\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:/) {
    return $1;
  }
  return undef;
}

sub constructor_name {
  my ($line) = @_;
  if ($line =~ /^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)\b/) {
    return $1;
  }
  return undef;
}

sub doc_comment_anchor_name {
  my ($lines, $line_number) = @_;
  return undef if $line_number < 1 || $line_number > scalar(@$lines);
  my $start = $line_number - 1;
  return undef if $lines->[$start] !~ m{/\--};

  my $end = $start;
  while ($end <= $#$lines && $lines->[$end] !~ m{-/}) {
    ++$end;
  }
  return undef if $end > $#$lines;

  for (my $i = $end + 1; $i <= $#$lines; ++$i) {
    next if $lines->[$i] =~ /^\s*$/;
    my $decl = declaration_name($lines->[$i]);
    return $decl if defined $decl;
    my $field = field_name($lines->[$i]);
    return $field if defined $field;
    return undef;
  }
  return undef;
}

sub anchor_name_at {
  my ($lines, $line_number) = @_;
  return undef if $line_number < 1 || $line_number > scalar(@$lines);
  my $line = $lines->[$line_number - 1];
  my $decl = declaration_name($line);
  return $decl if defined $decl;
  my $field = field_name($line);
  return $field if defined $field;
  my $constructor = constructor_name($line);
  return $constructor if defined $constructor;
  return doc_comment_anchor_name($lines, $line_number);
}

sub load_lean_anchor_index {
  find(
    {
      wanted => sub {
        my $path = $File::Find::name;
        return if $path !~ /\.lean\z/;
        return if $path =~ m{/(?:\.lake|lake-packages)/};

        my $lines = read_lines($path);
        my $rel = relative_path($path);
        for my $i (0 .. $#$lines) {
          my $name = declaration_name($lines->[$i]);
          $name = field_name($lines->[$i]) if !defined $name;
          $name = constructor_name($lines->[$i]) if !defined $name;
          next if !defined $name;
          push @{$lean_anchor_index{$name}}, {
            rel => $rel,
            line => $i + 1,
          };
        }
      },
      no_chdir => 1,
    },
    "$root/lean/Legitimacy"
  );
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

sub exact_matches {
  my ($symbol, $rel, $line_number) = @_;
  for my $anchor (@{$lean_anchor_index{$symbol} || []}) {
    return 1 if $anchor->{rel} eq $rel && $anchor->{line} == $line_number;
  }
  return 0;
}

sub expected_for {
  my ($symbol, $rel) = @_;
  my @matches =
    map { "`$symbol` at $_->{rel}:$_->{line}" }
    grep { $_->{rel} eq $rel }
    @{$lean_anchor_index{$symbol} || []};
  return @matches;
}

load_lean_anchor_index();

for my $doc_path (@doc_paths) {
  my $doc_rel = relative_path($doc_path);
  open my $dfh, "<", $doc_path or die "cannot read $doc_path: $!";
  my $content = do {
    local $/;
    <$dfh>;
  };
  close $dfh;

  while ($content =~ /(\S(?:.*?(?:\n(?!\s*\n).*?)*)?)(?:\n\s*\n|\z)/sg) {
    my $paragraph = $1;
    my $paragraph_start = $-[1];
    next if !defined $paragraph || $paragraph !~ /\S/;

    while ($paragraph =~ /(lean\/Legitimacy\/[A-Za-z0-9_\/.-]+\.lean):([0-9]+)/g) {
      my ($rel, $line_number) = ($1, int($2));
      my $cite_offset = $-[0];
      my $doc_line = offset_line_number($content, $paragraph_start + $cite_offset);
      my $source_path = "$root/$rel";
      ++$checked;

      if (!-f $source_path) {
        warn "$doc_rel:$doc_line: cited Lean file does not exist: $rel\n";
        ++$failures;
        next;
      }

      my $lines = read_lines($source_path);
      if ($line_number < 1 || $line_number > scalar(@$lines)) {
        warn "$doc_rel:$doc_line: cited line out of range: $rel:$line_number\n";
        ++$failures;
        next;
      }

      my $local_symbols =
        symbols_in_text(sentence_containing_offset($paragraph, $cite_offset));
      if (!%$local_symbols) {
        $local_symbols = symbols_in_text($paragraph);
      }
      my %candidate_symbols;
      for my $symbol (keys %$local_symbols) {
        next if !exists $lean_anchor_index{$symbol};
        for my $anchor (@{$lean_anchor_index{$symbol}}) {
          $candidate_symbols{$symbol} = 1 if $anchor->{rel} eq $rel;
        }
      }

      if (%candidate_symbols) {
        my $has_exact_match = 0;
        for my $symbol (keys %candidate_symbols) {
          if (exact_matches($symbol, $rel, $line_number)) {
            $has_exact_match = 1;
            last;
          }
        }
        next if $has_exact_match;

        for my $symbol (keys %candidate_symbols) {
          my @expected = expected_for($symbol, $rel);
          warn "$doc_rel:$doc_line: $rel:$line_number does not anchor named symbol "
            . "`$symbol`; expected " . join("; ", @expected) . "\n";
          ++$failures;
        }
        next;
      }

      my $anchored_name = anchor_name_at($lines, $line_number);
      if (!defined $anchored_name) {
        warn "$doc_rel:$doc_line: $rel:$line_number is not a Lean declaration, field, or doc-comment anchor\n";
        ++$failures;
      }
    }
  }
}

if ($failures) {
  die "doc Lean line citation check failed with $failures failure(s)\n";
}

print "doc Lean line citations: OK ($checked citations checked)\n";
PERL
