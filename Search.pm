
package MMM::Text::Search;

#$Id: Search.pm,v 1.43 1999/11/24 18:46:27 maxim Exp $
use strict;
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $verbose_flag  );
require Exporter;
require AutoLoader;
@ISA = qw(Exporter AutoLoader);
@EXPORT = qw(
);
$VERSION = '0.06';

#
# Perl module for indexing and searching text files and web pages.
# 		(Max Muzi, Apr-Sep 1999)
# 
#
# Note on implementation:
# The technique used for indexing is substantially derived from that
# exposed by Tim Kientzle on Dr. Dobbs magazine. (Actually IndexWords() 
# has been cut'n'pasted from his scripts.) 
#
# 

use DB_File;    
use Fcntl;   
require 5.005;

$verbose_flag = 0;

my $debug_flag = 0;

my $errstr = undef;
my $syntax_error = undef;

sub errstr { $errstr };

sub new { 			 # constructor!  (see the docs for usage [sorry, there're no docs ])
	my $pkg = shift;
	my $arg = shift;
	my $opt = undef;
	if (ref($arg) ne "HASH") { 
		if (-f $arg) {
			$opt->{IndexDB} = $arg;
			$opt->{Verbose} = shift;
		}
		else {	
			die "usage:   \$obj = new MMM::Text::Search ( '/index/path' or \$hashref)\n"    
		}
	} else {
		$opt = $arg;
	};

	$verbose_flag = $opt->{Debug} || $opt->{Verbose} ; 
	
	my $indexdbpath = $opt->{IndexDB} || $opt->{IndexPath} ;
	my $filemask 	= $opt->{FileMask} ;
	my $dirs 	= ( ref($opt->{Dirs}) eq "ARRAY" ) ? $opt->{Dirs} : [ ];
	my $followsymlinks = defined $opt->{FollowSymLinks};
	
	my $opturls =  $opt->{Urls} ||  $opt->{URLs};
	my $urls 	= ( ref($opturls) eq "ARRAY" ) ? $opturls : [ ];
	my $level	= int $opt->{Level};
	
	my $filesdbpath = $indexdbpath;
	$filesdbpath =~ s/(\.db)*$/\-files.db/;
	my $titlesdbpath = $indexdbpath;
	$titlesdbpath =~ s/(\.db)*$/\-titles.db/;
	
	my $minwordsize = $opt->{MinWordSize} || 1;


	my $self = {
		indexdbpath 	=> $indexdbpath,
		filesdbpath 	=> $filesdbpath,
		titlesdbpath	=> $titlesdbpath,
		filemask 	=> length($filemask) ? qr/$filemask/ : undef,
		dirs 		=> $dirs,
		followsymlinks  => $followsymlinks,
		minwordsize	=> $minwordsize,
		ignorelimit	=> $opt->{IgnoreLimit} || (2/3),
		urls		=> $urls,
		level		=> $level,
		url_exclude	=> $opt->{UrlExludeMask} || "(?i).*\.(zip|exe|gz|arj|bin|hqx)", 
		
	};
	DEBUG("filemask=$filemask, indexfile=$indexdbpath, ignorelimit=$self->{ignorelimit}\n");
	DEBUG("dirs = [", join(",", @$dirs),"], ");
	DEBUG("urls = [", join(",", @$urls),"] \n");
	bless($self, $pkg);
	return $self;
}

sub _add_keys_to_match_hash {  
# extract file-codes from $keys and update corresponding $hash elements (score)
	my ($keys, $hash) = @_;
	my $key;
	foreach $key ( unpack("n*",$keys) ) { 
#		DEBUG($key, " ");
		# ignored words (stop-words) only include file-id 0 (see FlushCache() below)
		return 0 if  $key == 0 ; 
		$hash->{$key}++
	}
	return 1;
}
	
sub _push_words_from_hash {
	my ($hash,$array, $regexp) = @_;
	my $w;
	for $w(keys %$hash) {
		push @$array,$w if $w =~ $regexp;
	}
}



#notes on advanced_query();
# - queries containing stop-words may yields bizzare results..
# - score is not always correct
# - error handling should be improved... :-)
sub advanced_query {
# perform queries such as  "( a and ( b or c ) ) and ( d and e) "
	my $self = shift;
	my $expr = shift;
	my $indexdbpath= $self->{indexdbpath};
	my $filesdbpath = $self->{filesdbpath};
	my $titlesdbpath = $self->{titlesdbpath};
	my %indexdb;
	my %filesdb;
	my %titlesdb;
	return undef unless (-f $indexdbpath && -r _);
	return undef unless (-f $filesdbpath && -r _);
	return undef unless (-f $titlesdbpath && -r _);
	return undef unless	
		tie_hash(\%indexdb,$indexdbpath, O_RDONLY ) &&
		 tie_hash(\%filesdb,$filesdbpath, O_RDONLY ) &&
		  tie_hash(\%titlesdb,$titlesdbpath, O_RDONLY );
	my @ignored = ();
	my @words = ();
	my $verbose_flag_tmp = $verbose_flag;
	$verbose_flag = shift; # undocumented debug switch
	chomp $expr;	
	undef $syntax_error; #reset error
	DEBUG("********** _match_expression() debug **********\n");	
	my $match = _match_expression($expr, \%indexdb, \@ignored);
	DEBUG("**********         end debug         **********\n");	
	if ($syntax_error) {
		$errstr = $syntax_error;
		$verbose_flag = $verbose_flag_tmp;
		return undef;
	}
	my $result =  _make_result_hash($match,\%filesdb, \%titlesdb, \@words, \@ignored);
	
	untie(%indexdb);
	untie(%filesdb);
	untie(%titlesdb);
	$verbose_flag = $verbose_flag_tmp;
	return $result;
}

sub _match_expression { 	 # recursively apply a keyword-search expression to indexdb
				 # $expr may be either a string or a ref to an array of tokens
				 # a ref to a "score" hash is returned (or undef sometimes)
	my ($expr, $index, $ignored) = @_;
	my $parsed = _parse_expression($expr);
		 # _parse_expression() returns a reference to an array of three elements:
		 # 			[ operator, left_expr, right_expr]
		 #  if right_expr is not defined then expr was atomic and left_expr is a string,
		 #  otherwise both right_expr and left_expr are references to arrays of tokens
	if ( not $parsed) {
		DEBUG("Syntax error :-( \n");
		return undef;
	}
	my ( $op, $left,$right) = @$parsed;
	
	if ($left && not $right) {  
		$left =~ s/^\s*\(?\s*|\s*\)?\s*$//g;
		DEBUG("Looking up >$left<\n");
		my %matches = ();
		my $word = $left;
		my $rc = 0;
    		my $keys = $index->{lc $word}; # get file-id's from indexdb
		$rc = _add_keys_to_match_hash($keys,\%matches);
		# if $rc is false then $word  is a stop-word, see _add_keys_to_match_hash() for more info		
		if (not $rc) {
			DEBUG("$word ignored\n");
			push @$ignored, $word;
			return undef;
			# what should we do now? gotta think it over...
		}
		return \%matches;
	}
	
	DEBUG("Evaluating >$left< --$op-- >$right<\n");
	my $left_match  = _match_expression($left, $index, $ignored);		
	my $right_match = _match_expression($right, $index, $ignored);		
	
	return undef if ($syntax_error); 
	my %matches = ();
	my $file = undef;
	
	if ($op eq 'AND' ) {
		%matches = ( %$left_match );
		for $file( keys %matches) {
			delete $matches{$file} unless $right_match->{$file}
		}
		return \%matches;
	}
	if ($op eq 'AND NOT') {
		%matches = ( %$left_match );
		for $file( keys %matches) {
			delete $matches{$file} if $right_match->{$file}
		}
		return \%matches;
	}
	if ($op eq 'OR')  {
		%matches = (  %$left_match );
		for $file( keys	%$right_match) {
			if ($matches{$file}) {
				$matches{$file} +=$right_match->{$file};
			} else {
				$matches{$file} =$right_match->{$file};
			}
		}
		return \%matches;
	}	
	return undef;
}	

sub _parse_expression {
	my $arg = shift;
	my $tokens = undef;  # this is an arry ref
	if (ref($arg) ne 'ARRAY') {
		$tokens = [ 
		 $arg =~  m/( \( | \)| \bAND\s+NOT\b | \bAND\b | \bOR\b | \"[^\"]+\" | \b\w+\b) /xig 
			];
	}
	 # important!!	"AND NOT" is treated as a single logical operator... 
	 # 		this means that things like "not a and b" aren't well-formed,
	 #		while "b and not a" is
	else { $tokens = $arg;
	}
	my $left =  undef; # array ref  (oppure stringa se è un espressione atomica)
	my $right = undef; # array ref !
	my $op =    'OR';
	my $depth = 0;
	my $pos = 0;
	my $tok;
	my $len = int @$tokens;
	DEBUG("expr = ", join(" + ", @$tokens),"\n"); 	
	while (1) {
		if ($len == 1) {
			return [ undef, $tokens->[0], undef ];
		}
		DEBUG("$tok : depth=$depth pos=$pos len=$len\n");
		if ($depth == 0 && ($pos == $len) ) {
			if ($tokens->[0] eq '(' && $tokens->[$len-1] eq ')') {
			 # take off outer parentheses...
				shift @$tokens;
				pop @$tokens;
				$len  -= 2;
				$pos   = 0;
				$depth = 0;
				DEBUG("expr = ", join(" + ", @$tokens),"\n"); 	
			} else { # ahhhh... this expression won't be parsed... 
				$syntax_error = "Ill-formed expression (\"".join(' ', @$tokens)."\")";
				DEBUG("atom not atomic\n");			
				return undef;
			}
	
		} elsif ( $pos == $len ) {
			$syntax_error = "Non-matching parentheses (\"".join(' ', @$tokens)."\")"; 
			DEBUG("non matching parentheses\n");
			return undef;
		}
		$tok = $tokens->[$pos++];
		if ($tok eq '(') { $depth++; next; }
		if ($tok eq ')') { $depth--; next; }
		next if $depth;
		if ($tok  =~ /\b(AND\s+NOT|AND|OR)\b/i) {
			if ($pos == 1 || $pos == $len)  {
				$syntax_error = "Ill-formed expression (\"".join(' ', @$tokens)."\")";
				return undef 
			} 
			$op = uc $1; $op =~ s/\s+/ /g;
			$left = [ @$tokens[0..$pos-2]    ];
			$right =  [ @$tokens[$pos..$len-1] ];
			DEBUG("right = ", join(" + ", @$right),"\n"); 	
			DEBUG("left  = ", join(" + ", @$left),"\n"); 	
			return [ $op, $left, $right ];
		}
	}
}
	
	

sub query { 	 # simple query....  	altavista +/- prefixes are recognized...
		 #			*/? globbing also works but 
		 #			slows query down significantly
		 #			globbing implicitly discards +/- prefix (it's a BUG!!!)
	my $self = shift;
	my $indexdbpath= $self->{indexdbpath};
	my $filesdbpath = $self->{filesdbpath};
	my $titlesdbpath = $self->{titlesdbpath};
	my %indexdb;
	my %filesdb;
	my %titlesdb;
	return undef unless (-f $indexdbpath && -r _);
	return undef unless (-f $filesdbpath && -r _);
	return undef unless (-f $titlesdbpath && -r _);
	return undef unless	
		tie_hash(\%indexdb,$indexdbpath, O_RDONLY ) &&
		tie_hash(\%filesdb,$filesdbpath, O_RDONLY ) &&
		tie_hash(\%titlesdb,$titlesdbpath, O_RDONLY );
	my %matches;
	my %limit;
	my %exclude;
	my @ignored;
	my $key;
	my $word;
	my $mustbe_words = 0;
	my @words = ();
	my $glob_regexp = undef;
	for (@_) {		# globbing feature... e.g. uni* passw?
		if ( /\*|\?/) {
			s/\*/\.\*/g;
			s/\?/\./g;
			$glob_regexp = $glob_regexp ? $glob_regexp."|^$_\$" : "^$_\$" ;
		}
		else {
			push @words, $_;
		}
	}
	if ($glob_regexp) {
		my $regexp = qr/$glob_regexp/;
		# collect  all words in db matching $glob_regexp and append them to the query
		_push_words_from_hash(\%indexdb, \@words, $regexp);
	}

	DEBUG("looking up ", join(", ", @words ), "\n");
	foreach $word (@words) {
		my $rc = 0;
#		DEBUG($word);
		if ($word =~ /^-(.*)/) {
    			my $keys = $indexdb{lc $1};
			$rc = _add_keys_to_match_hash($keys,\%exclude);
		} elsif ($word =~ /^\+(.*)/) {
			$mustbe_words++;
    			my $keys = $indexdb{lc $1};
			$rc = _add_keys_to_match_hash($keys,\%limit);
		} else {
    			my $keys = $indexdb{lc $word};
			$rc = _add_keys_to_match_hash($keys,\%matches);
		}
#		DEBUG("\n");
		if (not $rc) { push @ignored, $word }
	}
	
	if ($mustbe_words) {
		for $key(keys %limit) {
			next unless $limit{$key} >= $mustbe_words;
			$matches{$key}  += $limit{$key} ;
		}
		for $key(keys %matches) {
			delete $matches{$key} unless $limit{$key};
		}
	}
	for $key(keys %exclude) {
		delete $matches{$key};
	}
	my $result =  _make_result_hash(\%matches,\%filesdb, \%titlesdb, \@words, \@ignored);
	untie(%indexdb);
	untie(%filesdb);
	untie(%titlesdb);
	return $result;
}
	

sub _make_result_hash {
#            hash-ref  hash-ref   hash-ref    array-ref   array-ref
	my ( $match,   $filesdb,  $titlesdb,  $words,     $ignored  ) = @_; 
	my $result = {
		searched =>  $words,
		ignored  =>  $ignored,
		files	 =>  []
	};
	my $key;
	foreach $key (keys %$match) {
		my $ckey = pack("xn",$key);
  		my $name = $filesdb->{$ckey};
		my $title = $titlesdb->{$ckey};
		
		push @{ $result->{files} }, { 
			filename => $name,
			score 	 => $match->{$key},
			title	 => $title
		};
  		DEBUG("$name:  $match->{$key}\n");
	}
	return $result;
}


	
	
	


sub DEBUG (@) { $verbose_flag && print STDERR @_ };

sub tie_hash {
	my ($hashref, $file ,$perm) = @_;
	$perm = (O_RDWR|O_CREAT) unless defined $perm;
	my $rc = tied(%$hashref);
	return $rc if $rc;
	$rc = tie(%$hashref,'DB_File',$file, $perm, 0644, $DB_File::DB_BTREE) ;
	if ($debug_flag) {
			my $count = int keys %$hashref;
			DEBUG("tie $hashref ($rc) ($count keys)\n");
	} elsif ($verbose_flag) {
			DEBUG("tie $hashref ($rc)\n");
	}

		
	return $rc;
}

sub untie_hash {
	my ($hashref, $file ) = @_;
	if ($debug_flag) {
		my $count = int keys %$hashref;
		DEBUG("untie $hashref ($count keys)\n")
	}
	untie(%$hashref);
}


1;
#__END__

=head1 NAME

MMM::Text::Search - Perl module for indexing and searching text files and web objects

=head1 SYNOPSIS

  use MMM::Text::Search;
	  
  my $srch = new MMM::Text::Search {	#for indexing...
	#index main file location...  
		IndexPath => "/tmp/myindex.db",
	#local files...
		FileMask  => '(?i)(\.txt|\.htm.?)$',
		Dirs	  => [ "/usr/doc", "/tmp" ] ,
		FollowSymLinks => 0|1, (default = 0)
	#web objects...
		URLs	  => [ "http://localhost/", ... ],
		Level	  => recursion-level (0=unlimited)		
	#common options...		
		IgnoreLimit =>	0.3,   (default = 2/3)
		Verbose => 0|1				
  	};
  	
  $srch->makeindex;

  my $srch = new MMM::Text::Search (  #for searching....
		  "/tmp/myindex.db", verbose_flag );
  
  my $hashref = $srch->query("pizza","ciao", "-pasta" );  
  my $hashref = $srch->advanced_query("(pizza OR ciao) AND NOT pasta");  

  $srch->errstr()	# returns last error 
			# (only query syntax-errors for the moment being)

  
  $srch->dump_word_stats(\*FH)	

=head1 DESCRIPTION


=item	*
Indexing

makeindex() does all the job of indexing. When it's finished
the following files will have been created 
(assuming IndexPath = /path/myindex.db, see constructor):
 

	/path/myindex.db	 word index database
	/path/myindex-files.db	 filename/URL database
	/path/myindex-titles.db	 html title database
	/path/myindex.stopwords	 stop-words list
	/path/myindex.filelist	 readable list of indexed files/URLs
	/path/myindex.deadlinks	 broken http links

	[... lots of important things missing ... ]


dump_word_stats(\*FH) dumps all words sorted by occurence frequency using
FH file handle (or STDOUT if no parameter is specified). Stop-words get a 
frequency value of 1.

=item *
Searching

Both query() and advanced_query() return a reference to a hash with 
the following structure:

	(
	 ignored  => [ string, string, ... ], # ignored words
	 searched => [ string, string, ... ], # words searched for
	 files    => [  hashref, hashref, ... ] # list of files 
						# or URLs found
	 )
	
The 'files' element is a reference to an array of hashes, each having 
the following structure:

	(
 	 filename => string,  # file path or http URL
	 score    => number,  # score 
	 title    => string   # HTML title		 
	)

=head1 NOTES

Note on implementation:
The technique used for indexing is substantially derived from that
exposed by Tim Kientzle on Dr. Dobbs magazine. 

=head1 BUGS

Many, I guess. 

=head1 AUTHOR

Max Muzi <maxim@comm2000.it>

=head1 SEE ALSO

perl(1).

=cut



#
#-------------------- the following code is only used when indexing ----------------
#

sub dump_word_stats {
	my $self = shift;
	my $fh = shift || \*STDOUT;
	my $indexdbpath= $self->{indexdbpath};
	my %indexdb;
	die unless (-f $indexdbpath && -r _);
	tie_hash(\%indexdb,$indexdbpath, O_RDONLY );
	my %index = ( %indexdb );
	my $w;
	for $w( sort { length($index{$b}) <=> length($index{$a}) }
				keys %index ) {
		print $fh $w, "\t", length($index{$w}) / 2, "\n"; 
	}
	untie_hash(\%indexdb);
}


sub makeindex {
	my $self = shift;
	my $key = 0;
	my $indexdbpath = $self->{indexdbpath};
	my $filesdbpath = $self->{filesdbpath};
	my $titlesdbpath = $self->{titlesdbpath};

	my $dir;
	my $dirs 	= $self->{dirs};
	my $urls	= $self->{urls};
	my $filemask 	= $self->{filemask};
	my $keyref = \$key;
	my $filelistfile = $indexdbpath;
	$filelistfile =~  s/(\.db)?$/\.filelist/;
	open FILELIST, ">".$filelistfile;
	
	my $shared = {
		indexdbpath 	=> $indexdbpath,
		filesdbpath 	=> $filesdbpath,
		titlesdbpath 	=> $titlesdbpath,
		indexdb 	=> { },
		filesdb 	=> { },
		titlesdb 	=> { },
		cachedb 	=> { },
		filemask 	=> $filemask,
		current_key	=> 16, # first 16 values are reserved (0 = word is ignored)
		bytes		=> 0,
		count 		=> 0,
		filecount	=> 0,
		listfh		=> \*FILELIST,	
		status_THE 	=> 0,
		followsymlinks	=> $self->{followsymlinks},
		minwordsize	=> $self->{minwordsize},
		ignoreword	=> {},
		autoignore	=> 1,
		ignorelimit	=> $self->{ignorelimit} || (2/3),
		level		=> $self->{level},	
		url_exclude 	=> $self->{url_exclude}
	};
	
	unlink $indexdbpath."~"; 
	unlink $filesdbpath."~"; 
	unlink $titlesdbpath."~";
	tie_hash($shared->{indexdb}, $indexdbpath."~" )   or die "$indexdbpath: $!\n";
	tie_hash($shared->{filesdb}, $filesdbpath."~" )   or die $!;
	tie_hash($shared->{titlesdb},$titlesdbpath."~" ) or die $!;

	my $ignorefile = $indexdbpath;
	$ignorefile =~ s/(\.db)?$/\.stopwords/;
	if (-r $ignorefile) {  # read *-stopwords.dat file
		open F, $ignorefile;
		while (<F>) {
			chomp;
			s/^\s+|\s+$//g;
			$shared->{ignoreword}->{$_} = 1;
		}
		close F;
		my $count = int keys %{ $shared->{ignoreword} };
		DEBUG("using stop-words from $ignorefile ($count words)\n");
		$shared->{autoignore} = 0;
	}
	my $time = time();
	my $filecount = 0;
	DEBUG("Counting files...\n") if int @$dirs;
       	for $dir( sort  @$dirs) { $filecount += IndexDir($shared, $dir, 1); }
	$shared->{filecount} = $filecount;
	for $dir( sort  @$dirs) { IndexDir($shared, $dir); }
	for my $url( sort  @$urls) { IndexWeb($shared, $url); }
	FlushCache($shared->{cachedb}, $shared->{indexdb}, $shared);
	$time = time()-$time;
	DEBUG("$shared->{bytes} bytes read, $shared->{count} files processed in $time seconds\n");
	untie_hash($shared->{indexdb});
	untie_hash($shared->{filesdb});
	untie_hash($shared->{titlesdb});
	
	rename $indexdbpath."~", $indexdbpath; 
	rename $filesdbpath."~", $filesdbpath ;
	rename $titlesdbpath."~", $titlesdbpath;
	close FILELIST;
	if ( $shared->{autoignore} ) {
		open  F, ">".$ignorefile; #write *-stopwords.dat file
		print F join( "\n", sort keys %{ $shared->{ignoreword} } );
		close F;
	}

	return;	
 }


sub IndexDir {
	my ($shared, $dir, $only_recurse) = @_;
	my $followsymlinks = $shared->{followsymlinks};
	opendir D, $dir;
#	DEBUG "D $dir\n";
	my @files = readdir D;
	close D;
	my $e;
	my $count = 0;
	for $e(@files) {
		next if $e =~ /^\.\.?/;
		my $path = $dir."/".$e;
		if (-d $path) {
			unless ($followsymlinks) {
				next if -l $path ;
			}
			$count += IndexDir($shared,$path, $only_recurse);
		}
		elsif (-f _ ) {
			my $filemask = $shared->{filemask};
			if ($filemask) {
				next unless $e =~ $filemask;
			}
			unless ($only_recurse) {
				IndexFile($shared,$path);
			}
			$count ++;
		}
	}
	return $count;
}



sub IndexFile {
	my ($shared, $file, $text) = @_;
	my $cachedb = $shared->{cachedb};
	my $filesdb = $shared->{filesdb};
	my $key = $shared->{current_key};
	my $no_of_files = $shared->{filecount};
	DEBUG $shared->{count}+1, "/$no_of_files $file (id=$key)\n";
	my $fh = $shared->{listfh};
	print $fh "$key\t$file\n";
	local $/;
	unless (defined $text) {
		undef $/;
		open(FILE, $file);
		($text) = <FILE>; 		# Read entire file
		close FILE;
	}
	my $filesize =  length($text);
	if ($file =~ /\.s?htm.?/i ) {
		$text =~ /<title[^>]*>([^<]+)<\/title/i ;
		my $title = $1;
		$title =~ s/\s+/ /g;
		$shared->{titlesdb}->{pack"xn",$key} = $title;  # put title in db
		DEBUG("* \"$title\"\n");
		$text =~ s/<[^>]*>//g; 		# strip all HTML tags
	}
	# index all the words under the current file-id
	my($wordsIndexed) = &IndexWords($cachedb, $text,$key, $shared);
	$shared->{current_key}++;
	DEBUG "* $wordsIndexed words\n";
	
	# map file-id (key) to this filename
	$filesdb->{pack"xn",$key} = $file;   	# leading null is here for 
						# historical reasons :-)
	$shared->{bytes} += $filesize;
	$shared->{count}++;
	$shared->{_temp_size} += $filesize;
	if ($shared->{_temp_size} > 2000000 ) {
		my $rc = 0;
		$rc = FlushCache($cachedb, $shared->{indexdb}, $shared);
		
		if (! $rc ) {
			tie_hash($shared->{indexdb}, $shared->{indexdbpath}) or die $!;
			untie_hash($shared->{indexdb});
			$rc = FlushCache($cachedb, $shared->{indexdb}, $shared);
			die $! if not $rc;
		}
		
		$shared->{_temp_size} = 0;
		$shared->{cachedb} = {};
	}
}

sub IndexWords {
    my ($db, $words, $fileKey, $shared) = @_;
#      hash  content  file-id   options	
    my (%worduniq); # for unique-ifying word list
    my $minwordsize = $shared->{minwordsize};	    
    my (@words) = split( /[^a-zA-Z0-9\xc0-\xff\+\/\_]+/, lc $words); # split into an array of words
    @words = grep { $worduniq{$_}++ == 0 } 		# remove duplicates
             grep { length  > $minwordsize } 		# must be longer than one character
	     grep { s/^[^a-zA-Z0-9\xc0-\xff]+//; $_ }	# strip leading punct
             grep { /[a-zA-Z0-9\xc0-\xff]/ } 		# must have an alphanumeric
             @words;
					#   "  foreach (sort @words) { "
    for (@words) {     			# no need to sort here, 
	my $a = $db->{$_};		# we will sort when cache is flushed 
	$a .= pack "n",$fileKey;	# appending packed file-id's
        $db->{$_} = $a;
    }
    return int @words;
}



sub FlushCache { 
	my ($source, $dest, $shared) = @_;
		# flush source hashe into dest....  
		# %$dest is supposed to be tied, otherwise the whole
       		# thing doens't make much sense... :-)	
	my $scount = int  keys %$source ;
	my $ucount = 0;
	my $acount = 0;
	if ($scount == 0) {
		die "error: 0 words in cache\n";
	}
#	my $wordcount = int keys %$dest;
#	if ($wordcount < $shared->{wordcount}) {
#		warn "indexdb has lost entries (now $wordcount, were $shared->{wordcount}) \n";
#		return undef;
#	}
#	$shared->{wordcount} = $wordcount;
	
#	DEBUG("$wordcount words in database\n");
	my $objref = tied %$dest ;
	DEBUG("flushing $scount words into $dest ($objref)\n");
	
	my $filecount = $shared->{count};
	my $autoignore = $shared->{autoignore};
	my $ignorethreshold = int ( $filecount * $shared->{ignorelimit} );
		
	my $w;
	
	WORD:
	for $w(sort keys %$source) {
		my $data = $source->{$w};
		if ($shared->{ignoreword}->{$w} ) {
			DEBUG("ignoring '$w' \n");
			$data = pack("n*", ( 0 ) ); # id = 0 means $w is a stop-word
		}
		elsif (defined $dest->{$w}) {
			my %uniq = ();
			my $keys =  $dest->{$w} . $data ;
			my $keycount = length($keys)/2; # dividing by 2
			
			$ucount++;
##			my @keys = unpack("n*", $keys) ;
##			my $keycount = @keys;
##					
##			if ($keys[0] == 0 ) {  # skip ignored word 
##				DEBUG("skipping '$w' \n");
##				next WORD;
##			} els
			
			if ($autoignore && ($filecount > 100) 
			   && ($keycount > $ignorethreshold ) ) {
				DEBUG("word '$w' will be ignored (found in $keycount of $filecount files)\n");
				# ignored words are associated to file-id 0
##				@keys = ( 0 );
				$keys = pack("n*", 0);
				$shared->{ignoreword}->{$w} = 1;
			}
##			@keys = grep { $uniq{$_}++ == 0} @keys;
##			$data = pack("n*", @keys);
			
			$data = $keys;
			
##			if ($verbose_flag && ( $w eq "the" ) )  {
##				my $len = int(@keys);
##				if ($len < $shared->{status_THE} ) {
##						die "panic: problem with word 'the'";
##				}
##				$shared->{status_THE} = $len;
##				DEBUG("word 'the' found in $len files \n");
##			}

		} else {
			$acount++;
		}
		$dest->{$w} = $data;
		
#		if ($dest->{$w} ne $data) {
#			warn "unexpected error: \$w=$w\n";
#			return undef;
#		}
	}
	DEBUG("$ucount words updated, $acount new words added\n");
	if ($debug_flag) {
		my $wordcount = int keys %$dest;
		if ($wordcount < $shared->{wordcount}) {
			warn "indexdb has lost entries (now $wordcount, were $shared->{wordcount}) \n";
			return undef;
		}
		$shared->{wordcount} = $wordcount;
		DEBUG("$wordcount words in database\n");
	}
	return 1;
}





sub IndexWeb {
	my ($shared, $url) = @_;
	use MMM::Text::Search::Inet;
	my $req = new HTTPRequest { AutoRedirect => 1 };
	my %fetched = ();
	$req->set_url($url);
	my $host = $req->host();
	$shared->{req} = $req;
	$shared->{fetched} = \%fetched;
	$shared->{host} = $host;
	my $deadlinksfile = $shared->{indexdbpath};
	$deadlinksfile =~ s/(\.db)?$/\.deadlinks/;
	open DL, ">".$deadlinksfile;
	$shared->{deadlinksfh} = \*DL;
	recursive_fetch($shared, $url, "", 0);
}



sub recursive_fetch {
	my ($shared, $url, $parent, $level) = @_;
	my $req = $shared->{req};
	$req->reset();
	$req->set_url($url);
	my $url =  $req->url();
	return unless $req->host() eq $shared->{host};
	return if $shared->{fetched}->{$url};
	$shared->{fetched}->{$url} = 1;
	return unless $req->get_page();
	my $status =  $req->status();
	DEBUG( ">>> $url ($status)\n");
	if ( $status != 200 ) {
		my $fh = $shared->{deadlinksfh};
		my $url = $req->url();
		print $fh $status, "\t",
			$url, "(", $req->{_URL},")",
			"\t", $parent, "\n";
		return;	
	};
	my $base =  $req->base_url();
	my $content_ref = $req->content_ref();
	my $header  = $req->header();
	IndexFile($shared, $url, $$content_ref);
	return if ($shared->{level} && $level >= $shared->{level});
	$$content_ref =~ s/<!--.*?-->//gs;	#remove comments
	my @links = $$content_ref =~/href=([^>\s]+)/ig; #extract hyperlinks
	my $count = 0;
	my $exclude_re = $shared->{url_exclude};
	for(@links) {
		s/\"|\'//g;
		next if m/^(ftp|mailto|gopher|news):/;	
		next if m/^$exclude_re$/o;
		my $link = /^http/ ? $_ : join("/",$base,$_);
		$link =~ s/#.*//;
		$count++;
		recursive_fetch($shared,$link, $url, $level +  1); 
	}
}


1;
__END__
