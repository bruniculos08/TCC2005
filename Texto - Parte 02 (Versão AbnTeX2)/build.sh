#!/bin/bash


function compileLaTeX(){
       pdflatex -interaction=nonstopmode $1
       bibtex $1
       makeindex $1.idx
       makeindex $1.nlo -s nomencl.ist -o $1.nls
   	 makeglossaries $1
       pdflatex -interaction=nonstopmode $1
       pdflatex -interaction=nonstopmode $1
	# latexmk -pdf -time -silent $1
}

compileLaTeX "main"
# compileLaTeX $1