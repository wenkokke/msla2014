#encoding: utf-8
require 'rake/clean'

#set default configuration
FileName       = "Main"
StripImplicits = true
StripUnicode   = true

desc "Compile literate Agda into LaTeX (and optionally remove all implicit arguments)"
task :lhs2tex, [ :filename, :strip_implicits?, :strip_unicode? ] =>
  FileList['*.lagda'] + FileList['*.fmt'] do |t, args|

  args.with_defaults( :strip_implicits? => true )
  args.with_defaults( :strip_unicode? => true )

  # Check: input file exists
  unless File.exist? args.filename.ext('.lagda')
    fail "No such file #{ args.filename.ext('.lagda') }"
  end

  # Optionally: remove implicit types form the literate Agda.
  if args.strip_implicits? or args.strip_unicode?
    lhs = args.filename.ext('.lhs')
    src = IO.read( args.filename.ext('.lagda') , :encoding => 'utf-8' )
    src = strip_unicode( src )   if args.strip_unicode?
    src = strip_implicits( src ) if args.strip_implicits?
    IO.write( lhs , src , :encoding => 'utf-8' )
  else
    lhs = args.filename.ext('.lagda')
  end

  # Convert literate Agda to TeX (using lhs2TeX).
  system "lhs2TeX --agda #{ lhs } -o #{ args.filename.ext('.tex') }"

  fail "error in lhs2TeX" unless $?.success?
end

desc "Compile LaTeX into a Pdf using PdfLaTeX"
task :pdflatex , [ :filename , :strip_implcits? , :strip_unicode? ] =>
  FileList['*.bib'] do |t , args|

  task(:lhs2tex).invoke(args.filename, args.strip_implicits?, args.strip_unicode?)

  # Check: input file exists
  unless File.exist? args.filename.ext('.tex')
    fail "No such file #{ args.filename.ext('.tex') }"
  end

  system "pdflatex #{args.filename.ext('.tex')}"
  if $?.success?
    system "bibtex   #{args.filename}"
    system "pdflatex #{args.filename.ext('.tex')}"
    system "pdflatex #{args.filename.ext('.tex')}"
  end

  fail "error in pdfLaTeX" unless $?.success?
end

desc "Render the default literate Agda file (#{ FileName.ext('.lagda') }), and opens the result with a Pdf viewer"
task :default do

  task(:pdflatex).invoke(FileName)
  system "open #{ FileName.ext('.pdf') }"

end



# Cleanup directives.

CLEAN.include('*.lhs','*.log','*.ptb','*.blg','*.bbl','*.tex','*.aux','*.agdai')
CLOBBER.include('*.pdf')

# Implementation: strip_implicits

RE_IMPLICIT = /(?<!λ\s)(?<!record\s)\s*(∀\s*)?\{([^\}]*?)\}(\s*→)?/

def strip_implicits(src)
  src.gsub(/\\begin\{code\}(.*?)\\end\{code\}/m) do |m|
    "\\begin{code}#{ $1.gsub(RE_IMPLICIT,'') }\\end{code}"
  end
end

def strip_unicode(src)
  src.
    gsub('μ̃*','Ν*').
    gsub('μ̃' ,'Ν').
    gsub('μ*','Μ*').
    gsub('μ' ,'Μ').
    gsub('⇒','~>').
    gsub('⇐','<~').
    gsub('⇚','<=').
    gsub('⇛','=>')
end
