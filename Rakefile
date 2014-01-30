#encoding: utf-8
require 'rake/clean'

CodeDir = 'code'
SourceFiles = FileList[
  'IntuitionisticLogic.lagda'   ,
  'LinearLogic.lagda'           ,
  'LambekGrishinCalculus.lagda' ]



### Code ###

desc "Extract the code from the paper"
task :code => SourceFiles.pathmap("#{CodeDir}/%n.agda")

def to_lagda(task_name)
  task_name.sub("#{CodeDir}/",'').sub('.agda','.lagda')
end

rule(/#{CodeDir}.*\.agda/ => [ proc {|task_name| to_lagda(task_name) } ]) do |t|
  Dir.mkdir(CodeDir) unless File.exists?(CodeDir)
  cmd = "lhs2TeX --agda --code #{to_lagda(t.name)}-o #{t.name}"
  puts cmd
  system cmd
end


### Paper ###

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

  cmd = "lhs2TeX --agda #{ f_lhs } -o #{ f_tex }"
  puts cmd
  system cmd

  File.delete f_lhs

  fail "error in lhs2TeX" unless $?.success?
end



### Slides ###

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



### Cleanup ###

CLEAN.include('*.lhs','*.log','*.ptb','*.blg','*.bbl','*.aux','*.snm',
              '*.toc','*.nav','*.out','*.agdai','auto','paper.tex',
              SourceFiles.ext('.tex'))
CLOBBER.include('paper.pdf','slides.pdf')



### Utilities ###

# Regular expression that filters implicit arguments from Agda source.
RE_IMPLICIT = /(?<!λ\s)(?<!record)(?<!λ)\s*(∀\s*)?\{([^\}]*?)\}(\s*→)?/

# Strip implicits from literate Agda source.
def strip_implicits(src)
  src.gsub(/\\begin\{code\}(.*?)\\end\{code\}/m) do |m|
    "\\begin{code}#{ $1.gsub(RE_IMPLICIT,'') }\\end{code}"
  end
end

# Replaces certain unicode tokens that trip LaTeX up.
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
