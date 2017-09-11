#!/usr/bin/env perl

use warnings;
use strict;

use File::Slurp qw/read_file/;
use Data::Printer;
use Text::ANSITable;
use POSIX qw/round/;
use LaTeX::Table; 
use utf8::all;

my %stats;
my @csv = read_file $ARGV[0];
my @head = split /,/, shift @csv;
my @solvers = map {s/\s*+"(\s*+)//gr} @head[1 .. $#head];


foreach (@csv) {
   chomp;
   my ($goal, @time) = split /,/;
   next unless @time;
   foreach(@time) {
      $_ = undef if $_ eq '-1.';
   }
   if ($goal =~ m/^"WP_parameter (?<name>[a-z_]\w*)/) {
      my $fname = ($+{name} =~ s/_(0|ensures).*+//r);
      for(my $i = 0; $i < @time; ++$i) {
         push @{$stats{$fname}{$solvers[$i]}{time}}, $time[$i];
      }
   } else {
      die "unknown $goal";
   }
}

foreach my $f (keys %stats) {
   my $max = 0;
   foreach my $s (keys %{$stats{$f}}) {
      my $done = 0;
      my $total = 0;
      $max = @{$stats{$f}{$s}{time}} unless $max;
      foreach (@{$stats{$f}{$s}{time}}) {
         if ($_) {
            $total += $_;
            $done += 1;
         }
      }
      my $average = 0;
      $average = $total / $done if $done;
      $stats{$f}{$s}{done} = $done;
      $stats{$f}{$s}{total} = $total;
      $stats{$f}{$s}{average} = $average;
   }
   $stats{$f}{max} = $max;
}
my $column_names = ['Function', 'VC', @solvers];
my $table = Text::ANSITable->new;
$table->border_style('Default::bold');
$table->color_theme('Default::default_gradation');
$table->columns($column_names);
my @data = ['', 'total', map {('vc', 'atime')} @solvers];
push @data, [];

my $total_vc = 0;
my %solvers_total;
foreach my $f (sort keys %stats) {
   my $ff = substr($f, 0, 12);
   $ff .= '.' if length($f) > length($ff);
   $ff =~ s/_/\\_/g;
   my @stat;
   my @stat1;
   my $max = $stats{$f}{max};
   $total_vc += $max;
   my $vmax = -1;
   my $tmin = 100000;
   for (@solvers) {
      my $done = '-';
      my $avr  = '-';
      my $str = '  - | -';
      if ($stats{$f}{$_}{done}) {
         $done = $stats{$f}{$_}{done};
         #$done = "\N{CHECK MARK}" if $done == $max;
         $avr = $stats{$f}{$_}{average};
         push @{$solvers_total{$_}{time}}, @{$stats{$f}{$_}{time}};
         $str = sprintf("%3s | %0.2f", $done, $avr);
         $vmax = $done if $vmax < $done;
         $tmin = $avr if $tmin > $avr;
      }
      push @stat, $str;
      if ($done eq '-') {
         push @stat1, "$done:2c";
      } else {
         push @stat1, ($done, sprintf("%0.2f", $avr));
      }
   }
   for(my $i = 0; $i < @stat1; $i += 2) {
      unless ($stat1[$i] =~ /2c/){
         $stat1[$i] = "\\textbf{$stat1[$i]}" if $stat1[$i] == $vmax;
         $stat1[$i+1] = "\\textbf{$stat1[$i+1]}" if $stat1[$i+1] eq sprintf("%0.2f", $tmin);
      } else {
         $i -= 1;
      }
   }
   $table->add_row([$ff, $max, @stat]);
   push @data, [$ff, $max, @stat1];
}

push @data, [];

my @solv;
my @solv1;
my $vmax = -1;
my $tmin = 100000;
foreach(@solvers) {
   my $avr = 0.0;
   my @succ = grep defined, @{$solvers_total{$_}{time}};
   my $done = @succ;
   $avr += $_ for @succ;
   $avr /= $done;
   $avr = round($avr * 100) / 100.0;
   if ($vmax < $done) {
      $vmax = $done;
   }
   if ($tmin > $avr) {
      $tmin = $avr;
   }
   push @solv, sprintf("%4d | %0.2f", $done, $avr);
   push @solv1, ($done, sprintf("%0.2f", $avr));
}
for(my $i = 0; $i < @solv1; $i += 2) {
   if ($solv1[$i] == $vmax) {
      $solv1[$i] = "\\textbf{$solv1[$i]}";
   }
   if ($solv1[$i+1] == $tmin) {
      $solv1[$i+1] = "\\textbf{$solv1[$i+1]}";
   }
}
$table->add_row(['TOTAL', $total_vc, @solv]);
push @data, ['TOTAL', $total_vc, @solv1];
print $table->draw;

my $ltable = LaTeX::Table->new(
   {   
      filename    => 'bench.tex',
      maincaption => 'Solvers',
      caption     => 'Proofs Statistics',
      label       => 'table:bench',
      position    => 'tbp',
   }
);
my @snames = map {m/(\H++)/; "$1:2c"} @solvers;
my @svers = map {m/\(([^\)]++)/; "$1:2c"} @solvers;
$ltable->set_header([['Function', 'VC', @snames], ['', '', @svers]]);
#$ltable->set_theme('Houston');
$ltable->set_theme('Dresden');
#$ltable->set_theme('Berlin');
#$ltable->set_header([['Function', 'VC', @snames]]);
$ltable->set_data(\@data);
$ltable->generate(); 

