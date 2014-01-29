#encoding: utf-8
require 'rake/clean'

SourceFiles = FileList[
  'IntuitionisticLogic.lagda'   ,
  'LinearLogic.lagda'           ,
  'LambekGrishinCalculus.lagda' ]


desc "Compile and open the paper"
task :default => 'paper.pdf' do
  system "open paper.pdf"
end

desc "Compile the paper"
file 'paper.pdf' => [ 'paper.tex' , 'paper.preamble.tex' , 'paper.bib' ] + SourceFiles.ext('.tex') do

  system "pdflatex paper.tex"
  if $?.success?
    system "bibtex paper"
    if $?.success?
      system "pdflatex paper.tex"
      system "pdflatex paper.tex"
    end
  end
end

desc "Compile literate Agda to TeX (and remove implicits)"
rule '.tex' => [ '.lagda' ] do |t|

  f_lagda = t.name.ext('.lagda')
  f_lhs   = t.name.ext('.lhs')
  f_tex   = t.name.ext('.tex')

  src = IO.read( f_lagda , :encoding => 'utf-8' )
  src = strip_unicode( src )
  src = strip_implicits( src )
  IO.write( f_lhs , src , :encoding => 'utf-8' )

  system "lhs2TeX --agda #{ f_lhs } -o #{ f_tex }"

  File.delete f_lhs

  fail "error in lhs2TeX" unless $?.success?
end

# Slides

desc "Compile and open the slides"
task :slides => 'slides.pdf' do
  system "open slides.pdf"
end

desc "Compile the slides"
file 'slides.pdf' => [ 'slides.tex' , 'slides.code.tex' ] + SourceFiles.ext('.tex') do
  system "pdflatex slides.tex"
  if $?.success?
    system "pdflatex slides.tex"
  end
end

# Cleanup directives.

CLEAN.include('*.lhs','*.log','*.ptb','*.blg','*.bbl','*.aux','*.snm',
              '*.toc','*.nav','*.out','*.agdai','auto','paper.tex',
              SourceFiles.ext('.tex'))
CLOBBER.include('paper.pdf','slides.pdf')

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
