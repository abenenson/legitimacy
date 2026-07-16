#!/usr/bin/env bash
# Copyright (c) 2026 Adam Benenson. All rights reserved.
# Released under Apache 2.0 OR MIT license as described in the file LICENSE.
set -euo pipefail

# This gate is intentionally strict: when a claim-ledger entry names a
# declaration and cites a file:line anchor, that line must resolve to the named
# declaration. Stale anchors are failures, not release-note warnings.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if ! perl -Mstrict -Mwarnings - "$ROOT" <<'PERL'
my ($root) = @ARGV;
my $readme = "$root/README.md";
my $ledger = "$root/docs/claim-ledger.md";

open my $rfh, "<", $readme or die "cannot read $readme: $!";
my %headings;
while (my $line = <$rfh>) {
  if ($line =~ /^#+\s+(.+?)\s*$/) {
    my $heading = $1;
    $heading =~ s/\s+#+\s*$//;
    $headings{$heading} = 1;
  }
}
close $rfh;

open my $lfh, "<", $ledger or die "cannot read $ledger: $!";
my $failures = 0;
my $checked_path_lines = 0;
my $checked_declarations = 0;
my $line_number = 0;
my %source_cache;
my $pending_decl;

sub read_source {
  my ($rel, $ledger_line) = @_;
  return $source_cache{$rel} if exists $source_cache{$rel};

  my $path = "$root/$rel";
  if (!-f $path) {
    warn "docs/claim-ledger.md:$ledger_line: cited source file not found: $rel\n";
    ++$failures;
    $source_cache{$rel} = undef;
    return undef;
  }

  open my $fh, "<", $path or die "cannot read $path: $!";
  my @lines = <$fh>;
  close $fh;
  $source_cache{$rel} = \@lines;
  return \@lines;
}

sub lean_declaration_name {
  my ($line) = @_;
  return $1 if $line =~ /^\s*(?:noncomputable\s+)?
    (?:private\s+|protected\s+|partial\s+|unsafe\s+)*
    (?:def|theorem|lemma|structure|class|inductive|abbrev|instance|axiom|opaque)
    \s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b/x;
  return undef;
}

sub rust_declaration_name {
  my ($line) = @_;
  return $1 if $line =~ /^\s*(?:pub(?:\([^)]*\))?\s+)?
    (?:async\s+|unsafe\s+|const\s+)*
    fn\s+([A-Za-z_][A-Za-z0-9_]*)\b/x;
  return $1 if $line =~ /^\s*(?:pub(?:\([^)]*\))?\s+)?
    (?:struct|enum|trait|type|const|static|mod)\s+
    ([A-Za-z_][A-Za-z0-9_]*)\b/x;
  return undef;
}

sub declaration_name {
  my ($rel, $line) = @_;
  return lean_declaration_name($line) if $rel =~ /\.lean\z/;
  return rust_declaration_name($line) if $rel =~ /\.rs\z/;
  return undef;
}

sub active_declaration_at {
  my ($rel, $lines, $line_number) = @_;
  return (undef, undef) if $line_number < 1 || $line_number > scalar(@$lines);
  for (my $i = $line_number - 1; $i >= 0; --$i) {
    my $name = declaration_name($rel, $lines->[$i]);
    return ($name, $i + 1) if defined $name;
  }
  return (undef, undef);
}

sub declaration_base_name {
  my ($candidate) = @_;
  $candidate =~ s/^\s+|\s+\z//g;
  $candidate =~ s/^.*:://;
  $candidate =~ s/^.*\.//;
  return $candidate if $candidate =~ /\A[A-Za-z_][A-Za-z0-9_']*\z/;
  return undef;
}

sub declaration_exists {
  my ($rel, $lines, $base) = @_;
  for my $line (@$lines) {
    my $decl = declaration_name($rel, $line);
    next if !defined $decl;
    my $decl_base = declaration_base_name($decl);
    return 1 if defined($decl_base) && $decl_base eq $base;
  }
  return 0;
}

sub code_literals {
  my ($line) = @_;
  my @codes;
  while ($line =~ /`([^`\n]+)`/g) {
    my $code = $1;
    next if $code =~ /README\s+"/;
    next if $code =~ m{\A(?:lean/Legitimacy|src|tests|cli)/};
    push @codes, $code;
  }
  return @codes;
}

sub is_declaration_candidate {
  my ($code) = @_;
  return 0 if $code =~ /[\/\s]/;
  return 0 if $code =~ /\A[0-9]/;
  return $code =~ /\A[A-Za-z_][A-Za-z0-9_']*(?:(?:::|\.)[A-Za-z_][A-Za-z0-9_']*)*\z/;
}

while (my $line = <$lfh>) {
  ++$line_number;
  while ($line =~ /README "([^"\n]+)"/g) {
    my $heading = $1;
    next if $headings{$heading};
    warn "docs/claim-ledger.md:$line_number: README heading not found: "
      . "\"$heading\"\n";
    ++$failures;
  }

  while ($line =~ m{((?:lean/Legitimacy|src|tests|cli)/[A-Za-z0-9_./-]+\.(?:lean|rs)):([0-9]+)}g) {
    my ($rel, $target_line) = ($1, int($2));
    ++$checked_path_lines;
    my $lines = read_source($rel, $line_number);
    next if !defined $lines;

    if ($target_line < 1 || $target_line > scalar(@$lines)) {
      warn "docs/claim-ledger.md:$line_number: cited line is out of range "
        . "$rel:$target_line\n";
      ++$failures;
    }

    if (defined $pending_decl && $line_number - $pending_decl->{line} <= 4) {
      my $base = declaration_base_name($pending_decl->{code});
      if (defined $base) {
        ++$checked_declarations;
        if (!declaration_exists($rel, $lines, $base)) {
          warn "docs/claim-ledger.md:$line_number: declaration not found in "
            . "$rel for `$pending_decl->{code}` (searched `$base`)\n";
          ++$failures;
        } elsif ($target_line >= 1 && $target_line <= scalar(@$lines)) {
          my ($active, $active_line) =
            active_declaration_at($rel, $lines, $target_line);
          my $active_base = defined($active) ? declaration_base_name($active) : undef;
          if (defined($active_base) && $active_base ne $base) {
            warn "docs/claim-ledger.md:$line_number: $rel:$target_line "
              . "currently resolves near `$active` at line $active_line, "
              . "not `$base`\n";
            ++$failures;
          }
        }
      }
    }
  }

  for my $code (code_literals($line)) {
    next if !is_declaration_candidate($code);
    $pending_decl = { code => $code, line => $line_number };
  }

  while ($line =~ /\bline\s+([0-9]+)\b/g) {
    warn "docs/claim-ledger.md:$line_number: bare line reference is "
      . "not an auditable anchor: line $1\n";
    ++$failures;
  }
}
close $lfh;

if ($failures) {
  die "claim-ledger anchor check failed with $failures failure(s)\n";
}

print "claim-ledger anchors: OK ($checked_path_lines path-line anchors, "
  . "$checked_declarations declarations checked)\n";
PERL
then
  exit 1
fi
