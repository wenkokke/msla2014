#encoding: utf-8
require 'rake/clean'

desc "Compile literate Agda into LaTeX (and optionally remove all implicit arguments)"
rule '.tex' => [ '.lagda' , '.fmt' ] do |t|

  f_lagda = t.name.ext('.lagda')
  f_tex   = t.name.ext('.tex')
  f_lhs   = t.name.ext('.lhs')

  src = IO.read( f_lagda , :encoding => 'utf-8' )
  src = strip_unicode( src )
  src = strip_implicits( src )

  IO.write( f_lhs , src , :encoding => 'utf-8' )

  # Convert literate Agda to TeX (using lhs2TeX).
  system "lhs2TeX --agda #{ f_lhs } -o #{ f_tex }"

  fail "error in lhs2TeX" unless $?.success?
end

desc "Compile LaTeX into a Pdf using PdfLaTeX"
file 'main.pdf' => [ 'main.tex' , 'main.bib' , 'IntuitionisticLogic.tex' ,
                     'LinearLogic.tex' , 'LambekGrishinCalculus.tex' ] do

  system "pdflatex main.tex"
  if $?.success?
    system "bibtex main"
    system "pdflatex main.tex"
    system "pdflatex main.tex"
  end
end


task :default => 'main.pdf' do
  system "open main.pdf"
end



# Cleanup directives.

CLEAN.include('*.lhs','*.log','*.ptb','*.blg','*.bbl','*.tex','*.aux','*.agdai')
CLOBBER.include('*.pdf')

# Regular expression that filters implicit arguments from Agda source.
RE_IMPLICIT = /(?<!λ\s)(?<!record)(?<!λ)\s*(∀\s*)?\{([^\}]*?)\}(\s*→)?/

# Function that strips implicits from literate Agda source.
def strip_implicits(src)
  src.gsub(/\\begin\{code\}(.*?)\\end\{code\}/m) do |m|
    "\\begin{code}#{ $1.gsub(RE_IMPLICIT,'') }\\end{code}"
  end
end

# Function that replaces certain unicode tokens.
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
