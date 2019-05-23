NAME=pl-experiments
DOCDIR=.gh-pages

web:
	dune build lang/affe/affe_www.bc.js
	@cp _build/default/lang/affe/affe_www.bc.js www

$(DOCDIR)/.git:
	mkdir -p $(DOCDIR)
	cd $(DOCDIR) && (\
		git clone -b gh-pages git@github.com:Drup/$(NAME).git . \
	)

gh-pages: $(DOCDIR)/.git web
	git -C $(DOCDIR) pull
	cp -r www/* $(DOCDIR)/affe/
	git -C $(DOCDIR) add --all 
	git -C $(DOCDIR) commit -a -m "gh-page updates"
	git -C $(DOCDIR) push origin gh-pages
