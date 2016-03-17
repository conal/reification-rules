
%.pdf: %.dot Makefile
	dot -Tpdf $< -o $@

%.svg: %.dot Makefile
	dot -Tsvg $< -o $@

%.png: %.dot
	dot -Gdpi=200 -Tpng $< -o $@

figures/%.jpg: %.dot
	dot -Gdpi=200 -Tjpg $< -o $@

%.see: %
	open $<

.PRECIOUS: %.pdf
