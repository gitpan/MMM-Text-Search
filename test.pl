
chomp ( my $host = qx/hostname/ );

#$dirs      =         [ "/usr/doc"  ];  

$dirs      =     	[ "/usr"  ];  
$filemask  =		'(?i)\.(htm.?|txt)$|^README$';
$urls 	= 	[ "http://$host/" ];

$indexfile =  	"./.test_pl.db";

$SIG{INT} = sub { warn "exiting\n"; exit };

if (-f "./custom_test.pl" ) {
	print "Using custom_test.pl\n";
	require "./custom_test.pl";
}

use MMM::Text::Search;

if ( not -f $indexfile  ) {
	print "*** Hello! Thanks for using this module.\n";
	print "*** Please, choose which test you want to perform:\n";
	print "[1] index all files matching  /$filemask/  \n";
	print "    within the $dirs->[0] hierarchy\n";
	print "[2] recursively fetch and index all web pages on $urls->[0]\n";
	print "*** (Edit test.pl to specify a different directory, host or file mask)\n";
	print ": " ;
	my $c = int scalar <STDIN>;
	if ($c == 1 ) {
		$urls = [];
	}
	elsif ($c == 2) {
		$dirs = [];	
	}
	else { die "Bad choice\n"; }
	
	my $search = new MMM::Text::Search { 
		IndexDB 	=> $indexfile,
		FileMask	=> $filemask,
		Dirs 		=> $dirs,
		IgnoreLimit	=> 1/4,
		Verbose 	=> 1,
		URLs		=> $urls,	
	
	};

	
	$search->makeindex();
}
my $search = new MMM::Text::Search $indexfile, 0;
my $dumpfile = $indexfile.".dump";
unless (-f $dumpfile) {
	open F, ">".$dumpfile;
	print "dumping word stats in $dumpfile (this will take a while)\n";
	$search->dump_word_stats(\*F);
	close F;
}
print "\n";
print "*** Let's enjoy searching, now!  \n";
print "*** Queries including \"AND\"/\"OR\" keywords will be processed \n";
print "*** by advanced_query() method, otherwise query() is used.      \n";
print "*** --Examples--  simple: unix +passwd -system               \n";
print "***             advanced: ( windows OR dos ) AND NOT unix  \n";
while (1) {
	print "search? > ";
	my $line = <STDIN>;
	last if $line =~ /^\s*$/;
	if ($line =~ /\band\b|\bor\b/i) {
		print "searching using advanced_query() method\n";
		$result = $search->advanced_query($line,1);
	} else {
		$result = $search->query(split ' ', $line);
	}
	my $k;
	if ($result) {
		my $filename;
		my $score;
		my $title;
		format STDOUT_TOP =
Score            Filename                          Title
------------------------------------------------------------------------------- 
.

		format STDOUT =
@<<@<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<@<<<<<<<<<<<<<<<<<<<<<<<<<<<
$score,$filename,                                   $title
.
		for $k( sort { $a->{score} <=>  $b->{score} } @{ $result->{files} } ) {
			$filename = $k->{filename};
			$score = $k->{score};
			$title = $k->{title};
			write;
		}
		my $count = int  @{ $result->{files} };
		print "-- files found: $count \n";
		print "-- ignored words: ", join(", ", @{ $result->{ignored} }) ,"\n";
	} else {
		print "Error: ", $search->errstr, "\n";
	}
}
	
	

$loaded = 1;
print "ok 1\n";

######################### End of black magic.

# Insert your test code below (better if it prints "ok 13"
# (correspondingly "not ok 13") depending on the success of chunk 13
# of the test code):

BEGIN { $| = 1; print "1..1\n"; }
END {print "not ok 1\n" unless $loaded;}

__END__
#		FileMask	=> '(?i)\.(\d+\w*|n)$',
#		Dirs 		=> [ "/usr/man", "/usr/local/man", "/usr/X11/man"  ],
#		Dirs 		=> [ "/usr/man"  ],
