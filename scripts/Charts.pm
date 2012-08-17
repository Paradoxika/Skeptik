package Charts;

use strict;
use warnings;

use version; BEGIN { our $VERSION = qv('0.0') }

############################################################
# Constants
############################################################
use Readonly;


############################################################
# Export
############################################################
use base qw( Exporter );
our @EXPORT      = qw();
our @EXPORT_OK   = qw(square_size rec_width rec_height draw_x draw_mx draw_y);
our %EXPORT_TAGS = (
    all => \@EXPORT_OK,
);


############################################################
# Interface
############################################################

sub square_size { return  5 }
sub rec_width   { return 11 }
sub rec_height  { return  4 }

sub draw_x {
    # Type  : API
    # Descr : Draw X axis and divisions
    # Params: title, div, factor, width, height
    # Return: 
    # Throws: 
    my ($title, $div, $factor, $width, $height) = @_;

    my $step = $div * $factor;
    my @div = map { $_ * $div } (1..($width / $step));

    draw_mx($title, $width, $height, @div);


#    my $midwidth = $width / 2;
#
#    print "\\draw (0,0) -- ($width,0);\n";
#    print "\\node at ($midwidth,-0.6) {$title};\n" if (defined($title) and length($title));
#
#    my $step = $div * $factor;
#    for my $i (1..($width / $step)) {
#      my $pos = $i * $step;
#      print '\node [anchor=north] at (' . $pos . ',0) {\small ' . ($i * $div) . "};\n";
#      print '\draw (' . $pos . ',0) -- (' . $pos . ",0.1);\n";
#      print "\\draw [style=help lines] ($pos,0) -- ($pos,$height);\n";
#    }
}

sub draw_mx {
    # Type  : API
    # Descr : Draw X axis and divisions
    # Params: title, width, height, list of div
    # Return: 
    # Throws: 
    my ($title, $width, $height) = splice @_, 0, 3;

    my $midwidth = $width / 2;
    print "\\draw (0,0) -- ($width,0);\n";
    print "\\node at ($midwidth,-0.6) {$title};\n" if (defined($title) and length($title));

    my $step = $width / scalar(@_);
    my $x = $step;
    for my $div (@_) {
      print '\node [anchor=north] at (' . $x . ',0) {\small ' . $div . "};\n";
      print '\draw (' . $x . ',0) -- (' . $x . ",0.1);\n";
      print "\\draw [style=help lines] ($x,0) -- ($x,$height);\n";
      $x += $step;
    }
}


sub draw_y {
    # Type  : API
    # Descr : Draw Y axis and divisions
    # Params: title, div, factor, width, height
    # Return: 
    # Throws: 
    my ($title, $div, $factor, $width, $height) = @_;

    my $midheight = $height / 2;

    print "\\draw (0,0) -- (0,$height);\n";
    print "\\node [rotate=90] at (-2.5em,$midheight) {$title};\n" if (defined($title) and length($title));

    my $step = ($div * $factor) - 0.001;
    for my $i (1..($height / $step)) {
      my $pos = $i * $step;
      print '\node [anchor=east] at (0,' . $pos . ') {\small ' . ($i * $div) . "};\n";
      print '\draw (0,' . $pos . ') -- (0.1,' . $pos . ");\n";
      print "\\draw [style=help lines] (0,$pos) -- ($width,$pos);\n";
    }
}


############################################################
# Privates
############################################################


1;
__END__

=head1 NAME

scripts/Charts.pm - 

=head1 SYNOPSIS

    use scripts/Charts.pm;

=head1 DESCRIPTION



=head1 Functions

=head3

=head1 DIAGNOSTICS

=over

=item 

=back


=head1 DEPENDENCIES

L<>

=head1 BUGS AND LIMITATIONS

No bugs have been reported.

Please report any bugs or feature requests to C<< <jogo@matabio.net> >>.

=head1 AUTHOR

Joseph Boudou, C<< <jogo@matabio.net> >>

=head1 LICENCE AND COPYRIGHT

Copyright 2009 Joseph Boudou.

This module is free software; you can redistribute it and/or
modify it under the same terms as Perl itself. See L<perlartistic>.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
