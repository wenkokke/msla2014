#encoding: utf-8
require 'rake/clean'
require 'tmpdir'

LitDir = 'paper'
LitFile = /#{LitDir}\/.*\.lagda/
LitFiles = FileList[
  'paper/paper.lagda'                 ,
  'paper/IntuitionisticLogic.lagda'   ,
  'paper/LinearLogic.lagda'           ,
  'paper/LambekGrishinCalculus.lagda' ]

CodeDir   = 'code'
CodeFile  = /#{CodeDir}\/.*\.agda/
CodeFiles = LitFiles.pathmap("#{CodeDir}/%n.agda")

HtmlDir   = 'html'
HtmlFile  = /#{HtmlDir}\/.*\.html/
HtmlFiles = CodeFiles.pathmap("#{HtmlDir}/%n.html")

PaperFiles = FileList[
  'paper/paper.tex'    ,
  'paper/paper.bib'    ,
  'paper/preamble.tex' ]



### HTML ###

task 'gh-pages' => HtmlFiles do
  f_html = File.absolute_path( HtmlDir )

  Dir.mktmpdir do |tmp|
    Dir.chdir(tmp) do

      # get clean repository
      cmd = "git clone git@github.com:pepijnkokke/SubstructuralLogicsInAgda.git pages"
      puts cmd
      system cmd
      fail unless $?.success?

      # move into the repository
      Dir.chdir('pages') do
        cmd = "git checkout gh-pages"
        puts cmd
        system cmd
        fail unless $?.success?

        cmd = "cp -r #{ f_html } ."
        puts cmd
        system cmd
        fail unless $?.success?

        cmd = "git add html"
        puts cmd
        system cmd
        fail unless $?.success?

        cmd = "git commit -m 'automatically generated gh-pages branch'"
        puts cmd
        system cmd
        fail unless $?.success?

        cmd = "git push origin gh-pages"
        puts cmd
        system cmd
        fail unless $?.success?
      end
    end
  end
end

desc "Publish the HTML documentation to GitHub pages"
task :html => HtmlFiles

def code2html(task_name)
  task_name.sub("#{CodeDir}/","#{HtmlDir}/").sub('.agda','.html')
end

def html2code(task_name)
  task_name.sub("#{HtmlDir}/","#{CodeDir}/").sub('.html','.agda')
end

desc "Extract HTML documentation from Agda files"
rule HtmlFile => [ proc { |fn| html2code(fn) } ] do |t|

  f_html = File.absolute_path(t.name)
  f_agda = html2code(f_html)

  cmd = "agda -i $AGDA_HOME -i code --html #{ f_agda } --html-dir=#{ HtmlDir }"
  puts cmd
  system cmd

  fail unless $?.success?
end



### Code ###

desc "Extract the code from the paper"
task :code => CodeFiles

def code2lit(task_name)
  task_name.sub("#{CodeDir}/","#{LitDir}/").sub('.agda','.lagda')
end

def lit2code(task_name)
  task_name.sub("#{LitDir}/","#{CodeDir}/").sub('.lagda','.agda')
end

rule CodeFile => [ proc { |fn| code2lit(fn) } ]  do |t|

  Dir.mkdir(CodeDir) unless File.exists?(CodeDir)

  f_agda  = File.absolute_path(t.name)
  f_lagda = code2lit(f_agda)
  f_lhs   = f_lagda.ext('.lhs')
  f_dir   = File.dirname(f_lagda)

  Dir.chdir(f_dir) do

    src = IO.read( f_lagda , :encoding => 'utf-8' )
    src = add_spacing( src )
    IO.write( f_lhs , src , :encoding => 'utf-8' )

    cmd = "lhs2TeX --agda --code --no-pragmas #{ f_lhs } -o #{ f_agda }"
    puts cmd
    system cmd

    File.delete f_lhs

    fail unless $?.success?
  end
end



### Paper ###

desc "Compile and open the paper"
task :default => 'paper/paper.pdf' do
  system "open paper/paper.pdf"
end

desc "Compile the paper"
task :paper => 'paper/paper.pdf'

desc "Compile the paper"
file 'paper/paper.pdf' => PaperFiles + LitFiles.ext('.tex') do
  Dir.chdir(LitDir) do

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

    fail unless $?.success?
  end
end



### Cleanup ###

TempPats  = ['*.lhs','*.log','*.ptb','*.blg','*.bbl','*.aux','*.snm','*.toc',
             '*.nav','*.out','*.agdai','auto','paper.tex']
TempFiles = FileList.new(TempPats.map {|fn| File.join(LitDir,fn) })

CLEAN.include(LitFiles.ext('.tex'),TempFiles)
CLOBBER.include(HtmlDir,'paper/paper.pdf',CodeFiles)



### Utilities ###

# Regular expression that filters implicit arguments from Agda source.
RE_IMPLICIT = /(?<!record)(?<!λ)\s*(∀\s*)?\{([^\}]*?)\}(\s*→)?/

# Add spacing to literate Agda source.
def add_spacing(src)
  src.gsub(/\\begin\{code\}(.*?)\\end\{code\}/m) do |m|
    "\\begin{code}#{ $1 }\n\\end{code}"
  end
end

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
