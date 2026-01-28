doc:
	git checkout gh-pages
	git reset --hard master
	cargo doc
	cp -r target/doc doc
	git add --all
	git commit -m "doc(*): rebuilding docs `date -u +"%Y-%m-%dT%H:%M:%SZ"`"
	git push -f origin gh-pages
	git checkout master
