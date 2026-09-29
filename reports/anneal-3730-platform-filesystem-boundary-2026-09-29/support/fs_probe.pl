#!/usr/bin/env perl
use strict;
use warnings;
use Fcntl qw(:flock);

# All writes remain in one newly created directory beneath PROBE_ROOT.
my $root = $ENV{PROBE_ROOT} // die "PROBE_ROOT required\n";
my $dir = "$root/anneal-fs-probe-$$";
mkdir($dir, 0700) or die "mkdir $dir: $!";
my $current = "$dir/current";
my $staged = "$dir/staged";
my $lock = "$dir/lock";

sub put {
  my ($path, $data) = @_;
  open(my $fh, '>', $path) or die "open $path: $!";
  print {$fh} $data or die "write $path: $!";
  close($fh) or die "close $path: $!";
}
sub get_path {
  my ($path) = @_;
  open(my $fh, '<', $path) or return undef;
  local $/;
  my $v = <$fh>;
  close($fh);
  return $v;
}
sub get_fd {
  my ($fh) = @_;
  local $/;
  return scalar(<$fh>);
}
sub lock_child {
  my ($parent_fh) = @_;
  pipe(my $read_pipe, my $write_pipe) or die "pipe: $!";
  my $pid = fork();
  defined($pid) or die "fork: $!";
  if ($pid == 0) {
    close($read_pipe);
    close($parent_fh);
    open(my $other, '>>', $lock) or die "child lock open: $!";
    my $ok = flock($other, LOCK_EX | LOCK_NB) ? 1 : 0;
    print {$write_pipe} "$ok\n";
    close($write_pipe);
    close($other);
    exit(0);
  }
  close($write_pipe);
  my $answer = <$read_pipe>;
  close($read_pipe);
  waitpid($pid, 0);
  defined($answer) or die "child lock result missing";
  chomp($answer);
  return $answer;
}

put($current, "OLD_GENERATION\n");
open(my $old_fd, '<', $current) or die "open old: $!";
put($staged, "NEW_GENERATION\n");
rename($staged, $current) or die "replace: $!";
my $old_after_replace = get_fd($old_fd);
my $new_path = get_path($current);
close($old_fd);
open(my $new_fd, '<', $current) or die "open new: $!";
unlink($current) or die "unlink: $!";
my $new_after_unlink = get_fd($new_fd);
my $missing_after_unlink = !-e $current ? 1 : 0;
close($new_fd);
print "replace_old_fd\t$old_after_replace";
print "replace_new_path\t$new_path";
print "unlink_open_fd\t$new_after_unlink";
print "unlink_path_missing\t$missing_after_unlink\n";

open(my $parent_lock, '>>', $lock) or die "parent lock open: $!";
flock($parent_lock, LOCK_EX | LOCK_NB) or die "parent lock failed: $!";
my $contended = lock_child($parent_lock);
flock($parent_lock, LOCK_UN) or die "parent unlock failed: $!";
my $released = lock_child($parent_lock);
close($parent_lock);
print "flock_child_while_held\t$contended\n";
print "flock_child_after_release\t$released\n";

# Repeated same-directory rename(2) with two independent readers. This is a
# bounded sample, not a proof of atomicity for all schedules or crash durability.
put($current, "OLD_GENERATION\n");
my @pipes;
my @children;
for my $reader (1, 2) {
  pipe(my $rp, my $wp) or die "reader pipe: $!";
  my $pid = fork();
  defined($pid) or die "reader fork: $!";
  if ($pid == 0) {
    close($rp);
    my ($old, $new, $invalid, $missing) = (0, 0, 0, 0);
    for my $i (1..1200) {
      my $v = get_path($current);
      if (!defined($v)) { $missing++; }
      elsif ($v eq "OLD_GENERATION\n") { $old++; }
      elsif ($v eq "NEW_GENERATION\n") { $new++; }
      else { $invalid++; }
      select(undef, undef, undef, 0.00025);
    }
    print {$wp} "$old\t$new\t$invalid\t$missing\n";
    close($wp);
    exit(0);
  }
  close($wp);
  push @pipes, $rp;
  push @children, $pid;
}
select(undef, undef, undef, 0.01);
for my $i (1..300) {
  put($staged, ($i % 2) ? "NEW_GENERATION\n" : "OLD_GENERATION\n");
  rename($staged, $current) or die "stress rename $i: $!";
  select(undef, undef, undef, 0.0005);
}
my ($old_total, $new_total, $invalid_total, $missing_total) = (0, 0, 0, 0);
for my $rp (@pipes) {
  my $line = <$rp>;
  defined($line) or die "reader result missing";
  my ($o, $n, $i, $m) = split(/\t/, $line);
  $old_total += $o; $new_total += $n;
  $invalid_total += $i; $missing_total += $m;
  close($rp);
}
for my $pid (@children) { waitpid($pid, 0); }
print "sampled_old_reads\t$old_total\n";
print "sampled_new_reads\t$new_total\n";
print "sampled_invalid_reads\t$invalid_total\n";
print "sampled_missing_reads\t$missing_total\n";
die "reader control missed an old/new state\n" unless $old_total > 0 && $new_total > 0;
die "torn or missing read observed\n" if $invalid_total || $missing_total;
die "open/unlink/lock control mismatch\n"
  unless $old_after_replace eq "OLD_GENERATION\n"
      && $new_path eq "NEW_GENERATION\n"
      && $new_after_unlink eq "NEW_GENERATION\n"
      && $missing_after_unlink == 1
      && $contended == 0 && $released == 1;

unlink($current) or die "cleanup current: $!";
unlink($lock) or die "cleanup lock: $!";
rmdir($dir) or die "cleanup directory: $!";
print "cleanup_complete\t1\n";
