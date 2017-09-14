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
my %skip_solvers = (
   "Alt-Ergo (1.30 -Em)" => undef,
   "CVC4 (1.5 SPARK)" => undef,
   "Z3 (4.5.0 noBV)" => undef
);
my @solvers = map {s/\s*+"(\s*+)//gr} @head[1 .. $#head];
my @ssolvers = grep {! exists $skip_solvers{$_} } @solvers;


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
         if (defined $time[$i]) {
            if ($time[$i] + 0.0 > 40.0) {
               print "Timelimit exceed: $fname $solvers[$i] $time[$i]\n";
               $time[$i] = undef;
            }
         }
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
my $column_names = ['Function', 'VC', @ssolvers];
my $table = Text::ANSITable->new;
$table->border_style('Default::bold');
$table->color_theme('Default::default_gradation');
$table->columns($column_names);
my @data = ['', 'total', map {('vc', 'atime')} @ssolvers];
push @data, [];

=comment
\uline{important} underlined text like important
\uuline{urgent} double-underlined text like urgent
\uwave{boat} wavy underline like
\sout{wrong} line struck through word like wrong
\xout{removed} marked over like
\dashuline{dashing} dashed underline like dashing
\dotuline{dotty} dotted underline like
=cut

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
   my $vmin = 100000;
   my $tmax = -1;
   my $vmax = -1;
   my $tmin = 100000;
   for (@ssolvers) {
      my $done = '$\varnothing$';
      my $avr  = '-';
      my $str = ' - | -';
      if ($stats{$f}{$_}{done}) {
         $done = $stats{$f}{$_}{done};
         $avr = $stats{$f}{$_}{average};
         $vmin = $done if $vmin > $done;
         $vmax = $done if $vmax < $done;
         $tmin = $avr if $tmin > $avr;
         $tmax = $avr if $tmax < $avr;

         $done = '\checkmark' if $done == $max;
         push @{$solvers_total{$_}{time}}, @{$stats{$f}{$_}{time}};
         $str = sprintf("%3s | %0.2f", $done, $avr);
      }
      push @stat, $str;
      if ($done eq '$\varnothing$') {
         push @stat1, "$done:2c";
      } else {
         push @stat1, ($done, sprintf("%0.2f", $avr));
      }
   }
   for(my $i = 0; $i < @stat1; $i += 2) {
      unless ($stat1[$i] =~ /2c/){
         if ($stat1[$i] == $vmax) {
            $stat1[$i] = "\\textbf{$stat1[$i]}"
            #$stat1[$i] = "$stat1[$i]+"
         } elsif ($stat1[$i] == $vmin) {
            $stat1[$i] = "\\textit{$stat1[$i]}"
            #$stat1[$i] = "$stat1[$i]-"
         }
         if ($stat1[$i+1] eq sprintf("%0.2f", $tmin)) {
            $stat1[$i+1] = "\\underline{$stat1[$i+1]}"
         } elsif ($stat1[$i+1] eq sprintf("%0.2f", $tmax)) {
            $stat1[$i+1] = "\\dashuline{$stat1[$i+1]}"
         }
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
foreach(@ssolvers) {
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
      $solv1[$i+1] = "\\underline{$solv1[$i+1]}";
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
my @snames = map {m/(\H++)/; "$1:2c"} @ssolvers;
my @svers = map {m/\(([^\)]++)/; "$1:2c"} @ssolvers;
$ltable->set_header([['Function', 'VC', @snames], ['', '', @svers]]);
#$ltable->set_theme('Houston');
$ltable->set_theme('Dresden');
#$ltable->set_theme('Berlin');
#$ltable->set_header([['Function', 'VC', @snames]]);
$ltable->set_data(\@data);
$ltable->generate(); 

