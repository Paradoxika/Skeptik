EXCLUDE  :=
ifneq (,$(wildcard Makefile.local))
  include Makefile.local
endif

DOC	 :=     $(filter-out $(EXCLUDE), \
			$(shell egrep -l '^[^%]*\\begin\{document\}' *.tex))
ifneq ($(DOC),"")
	SL  	 :=     $(shell egrep -l '^[^%]*\\documentclass.*\{beamer\}' $(DOC))
	LNCS     :=     $(shell egrep -l '^[^%]*\\documentclass.*\{llncs\}' $(DOC))
	SRC      :=     $(filter-out $(SL), $(DOC))
endif
FIG      :=     $(wildcard *.fig)
PDFTEX   :=     $(FIG:%.fig=%.pdftex_t)

# PF Normal texts
# LNCS format is handled differently for 2/page
ifneq ($(SRC),)
  BIB      :=   $(shell egrep -l '^[^%]*\\bibliography' $(SRC))
  OBJ_PDF  :=	$(SRC:%.tex=%.pdf)
  OBJ_2_LNCS := $(LNCS:%.tex=%-2.pdf)
  OBJ_2    :=	$(filter-out $(OBJ_2_LNCS), $(SRC:%.tex=%-2.pdf))
endif

# PF Beamer texts
SL_4     :=	$(SL:%.tex=%-2x2.pdf)
SL_8     :=	$(SL:%.tex=%-2x4.pdf)
SL_PDF	 :=	$(SL:%.tex=%.pdf)

OBJS     :=	$(PDFTEX) \
		$(OBJ_2) $(OBJ_2_LNCS) $(OBJ_PDF) \
		$(SL_PDF) $(SL_4) $(SL_8)

all 	: $(OBJS)

$(OBJ_PDF) $(SL_PDF):	%.pdf : %.tex
	TARGET=$<; TARGET=$${TARGET%%.tex}; \
	pdflatex $<; \
        if egrep -s "No file $${TARGET}.bbl" $${TARGET}.log; then \
          bibtex $${TARGET}; pdflatex $${TARGET}; \
	fi; \
        if egrep -s "No file $${TARGET}.toc" $${TARGET}.log; then \
	  pdflatex $${TARGET}; \
	fi; \
        if egrep -s ".*Citation .* undefined" $${TARGET}.log; then \
          bibtex $${TARGET}; pdflatex $${TARGET}; \
	fi; latex_count=5; \
	while egrep -s "Rerun to get cross-references right" $${TARGET}.log && [ $$latex_count -gt 0 ] ;\
	    do \
	      pdflatex $${TARGET}.tex ; latex_count=$$(( $$latex_count - 1 )); \
	    done

$(OBJ_2):	%-2.pdf : %.pdf
	pdfnup --nup 1x2 $< --outfile $@

$(OBJ_2_LNCS):	%-2.pdf : %.pdf
	pdfnup --nup 1x2 $< --outfile $@

# DOES NOT WORK
$(SL_4):     	%-2x2.pdf : %.pdf
	pdfnup --nup "2x2" --offset ".25cm .25cm" --delta ".25cm .5cm" \
	  --orient portrait --frame true --scale 2 $< 

$(SL_8):    	%-2x4.pdf : %.pdf
	pdfnup --nup "2x4" --offset ".25cm .25cm" --delta ".25cm .5cm" \
	  --frame true --scale .95 $<

# Could use targets, but less freedom to reach fixpoint in latex

$(PDFTEX) :	%.pdftex_t : %.fig
	TARGET=$<; TARGET=$${TARGET%%.fig}; \
	LANG=en_US; fig2dev -L pdftex $< > $${TARGET}.pdf ; \
	LANG=en_US; fig2dev -L pdftex_t -p $${TARGET}.pdf $< > $@ \
#	sed "s/col11 {0.530 0.810 1.000 srgb}/col11 {0.700 0.700 0.700 srgb}/" $@ > tmp; \
#	  mv tmp $@
#	sed "s/\[rgb\]{0,.56,0}/[rgb]{.7,.7,.7}/" $@_t > tmp; mv tmp $@_t

clean :
	rm -f *~ missfont.log *.fig.bak
	rm -f $(FIG:%.fig=%.pdf) $(FIG:%.fig=%.pdftex_t)
	rm -f $(OBJS)
	rm -f $(SRC:%.tex=%.aux) $(SRC:%.tex=%.bbl) $(SRC:%.tex=%.blg) $(SRC:%.tex=%.log)
	rm -f $(SRC:%.tex=%.out) $(SRC:%.tex=%.idx) $(SRC:%.tex=%.ilg) $(SRC:%.tex=%.ind)
	rm -f $(SRC:%.tex=%.toc) $(SRC:%.tex=%.d)
	rm -f $(SL:%.tex=%.aux) $(SL:%.tex=%.bbl) $(SL:%.tex=%.blg) $(SL:%.tex=%.log)
	rm -f $(SL:%.tex=%.out) $(SL:%.tex=%.idx) $(SL:%.tex=%.ilg) $(SL:%.tex=%.ind)
	rm -f $(SL:%.tex=%.toc) $(SL:%.tex=%.d)
	rm -f $(SL:%.tex=%.nav) $(SL:%.tex=%.snm) $(SL:%.tex=%.vrb)
