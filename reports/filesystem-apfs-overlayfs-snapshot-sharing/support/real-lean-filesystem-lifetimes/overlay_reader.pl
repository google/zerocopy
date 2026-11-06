use strict;
use warnings;
my $root = '/tmp/lean-life';
my $path = "$root/Dep.olean";
open(my $fh, '<', $path) or die "open $path: $!";
binmode($fh);
my $len = -s $fh;
my $addr = syscall(9, 0, $len, 1, 2, fileno($fh), 0); # x86_64 Linux mmap, PROT_READ, MAP_PRIVATE
die "mmap failed" if $addr == -1;
open(my $mem, '<', '/proc/self/mem') or die "self mem: $!";
open(my $ready, '>', "$root/ready") or die $!; print $ready 'ready'; close($ready);
sub wait_for {
  my ($path) = @_;
  for (1..1200) { return if -e $path; select(undef,undef,undef,.01); }
  die "timeout waiting for $path";
}
for my $phase (1,2) {
  wait_for("$root/go$phase");
  sysseek($mem, $addr, 0) or die "seek mapped: $!";
  my $mapped=''; my $got=sysread($mem,$mapped,$len);
  die "short mmap read" unless defined($got) && $got == $len;
  seek($fh,0,0) or die "seek fd: $!";
  my $fd=''; $got=read($fh,$fd,$len);
  die "short fd read" unless defined($got) && $got == $len;
  open(my $mo,'>',"$root/phase${phase}-map.bin") or die $!; binmode($mo); print $mo $mapped; close($mo);
  open(my $fo,'>',"$root/phase${phase}-fd.bin") or die $!; binmode($fo); print $fo $fd; close($fo);
  open(my $ack,'>',"$root/ack$phase") or die $!; print $ack 'ack'; close($ack);
}
my $unmapped=syscall(11,$addr,$len); # x86_64 Linux munmap
die "munmap failed" if $unmapped != 0;
print "mapped_bytes=$len phases=2\n";
