#encoding: utf-8
require 'rake/clean'

# configuration
MAIN = "Main"

# 1. Compile the literate Agda into LaTeX.
task :mktex, [:show_implicits?] =>
  [ MAIN.ext('.lagda') ] + FileList['*.fmt'] do |t, args|
  args.with_defaults( :show_implicits? => false )

  # Optionally: remove implicit types form the literate Agda.
  if args.show_implicits?
    main_lagda = MAIN.ext('.lagda')
  else
    main_lagda = MAIN.ext('.no_implicits')
    src = IO.read( MAIN.ext('.lagda') , :encoding => 'utf-8' )
    src = no_implicits( src )
    IO.write( main_lagda , src , :encoding => 'utf-8' )
  end

  # Convert literate Agda to TeX (using lhs2TeX).
  system "lhs2TeX --agda #{main_lagda} -o #{MAIN.ext('.tex')}"
end

file MAIN.ext('.tex') => :mktex

# 2. Compile the LaTeX into a Pdf using PdfLaTeX.
task :mkpdf => [ :mktex ] + FileList['*.bib'] do
  system "pdflatex #{MAIN.ext('.tex')}"
  system "bibtex #{MAIN}"
  system "pdflatex #{MAIN.ext('.tex')}"
  system "pdflatex #{MAIN.ext('.tex')}"
end

file MAIN.ext('.pdf') => :mkpdf

# 3. Open the created Pdf file using the default Pdf viewer.
task :default => :mkpdf do
  system "open #{MAIN.ext('.pdf')}"
end



# Cleanup directives.

CLEAN.include('*.lhs','*.log','*.ptb','*.blg','*.bbl','*.tex','*.aux','*.agdai')
CLOBBER.include('*.pdf')

# Implementation of the 'no-implicits' task.

RE_IMPLICIT = /(?<!λ\s)(?<!record\s)(∀\s*)?\{(.*?)\}(\s*→)?\s*/

def no_implicits(src)
  src.gsub(/\\begin\{code\}(.*?)\\end\{code\}/m) do |m|
    "\\begin{code}#{ $1.gsub(RE_IMPLICIT,'') }\\end{code}"
  end
end
