#encoding: utf-8
require 'rake/clean'

CodeDir = 'code'
AgdaFiles = FileList[
  'paper/IntuitionisticLogic.lagda'   ,
  'paper/LinearLogic.lagda'           ,
  'paper/LambekGrishinCalculus.lagda' ]
PaperFiles = FileList[
  'paper/paper.tex'  ,
  'paper/paper.bib'    ,
  'paper/preamble.tex' ]



### Code ###

desc "Extract the code from the paper"
task :code => AgdaFiles.pathmap("#{CodeDir}/%n.agda")

def to_lagda(task_name)
  task_name.sub("#{CodeDir}/",'').sub('.agda','.lagda')
end

rule(/#{CodeDir}.*\.agda/ => [ proc {|task_name| to_lagda(task_name) } ]) do |t|
  Dir.mkdir(CodeDir) unless File.exists?(CodeDir)
  p t
  cmd = "lhs2TeX --agda --code #{to_lagda(t.name)} -o #{t.name}"
  puts cmd
  system cmd
end


### Paper ###

desc "Compile and open the paper"
task :default => 'paper/paper.pdf' do
  system "open paper/paper.pdf"
end

desc "Compile the paper"
file 'paper/paper.pdf' => PaperFiles + AgdaFiles.ext('.tex') do
  Dir.chdir("paper") do

    system "pdflatex paper.tex"
    if $?.success?
      system "bibtex paper"
      if $?.success?
        system "pdflatex paper.tex"
        system "pdflatex paper.tex"
      end
    end

  end
end

desc "Compile literate Agda to TeX (and remove implicits)"
rule '.tex' => [ '.lagda' ] do |t|

  f_abs   = File.absolute_path(t.name)
  f_lagda = f_abs.ext('.lagda')
  f_lhs   = f_abs.ext('.lhs')
  f_tex   = f_abs.ext('.tex')
  f_dir   = File.dirname(f_abs)

  Dir.chdir(f_dir) do

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
end



### Cleanup ###

CLEAN.include('*.lhs','*.log','*.ptb','*.blg','*.bbl','*.aux','*.snm',
              '*.toc','*.nav','*.out','*.agdai','auto','paper.tex',
              AgdaFiles.ext('.tex'))
CLOBBER.include('paper.pdf','slides.pdf','code')



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
