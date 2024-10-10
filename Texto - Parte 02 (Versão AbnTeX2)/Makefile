FLAGS = -f -shell-escape -pdf -quiet 
# FLAGS  = -f -pdf -pv -quiet
CLEANFLAG = -c
TARGET = main.tex
EXTRACLEAN = *.maf *.mtc* *.tdo *.nls *.nlo

all: 
	latexmk ${FLAGS} ${TARGET}

cleanall: changevar clean

changevar:
	$(eval CLEANFLAG=-C -bibtex)

clean:
	latexmk ${CLEANFLAG}; rm ${EXTRACLEAN}; cd PreTextual/; latexmk ${CLEANFLAG}; cd ../Partes/; latexmk ${CLEANFLAG}; cd ..