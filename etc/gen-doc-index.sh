#!/bin/bash

set -e

cd public
cp dev/*/index.html index.html

awk -i inplace '{if ($0 ~ /button>$/) {printf "%s", $0; next}; print}' index.html
awk -i inplace '{print gensub(/('\''|")\.\.\//, "\\1dev/", "g")}' index.html
awk -i inplace '{
gsub(/<\/nav>/, "\013")
sub(/<div class="block[^\013]*\013/, "\013")
sub(/<nav class="sub[^\013]*\013/, "")
gsub(/\013/, "</nav>")

sub(/dev\/[^/]*\/index.html/, "index.html")

gsub(/<\/h1>/, "\013")
sub(/<h1 class="fqn[^\013]*\013/, "")
gsub(/\013/, "</h1>")

gsub(/<\/script>/, "\013")
sub(/<script src="[^"]*main\.js[^\013]*\013/, "")
gsub(/\013/, "</script>")

print
}' index.html
awk -i inplace '{
if ($0 ~ /<\/h1>/) {
    print gensub(/(.*<\/h1>).*/, "\\1", 1)
    sub(/.*<\/h1>/, "")
    while ($0 !~ /<\/section>/) { getline }
    while (getline line<"../etc/index-contents.html") { print line }
    gsub(/<\/section>/, "\013")
    sub(/^[^\013]*/, "</div>")
    gsub(/\013/, "</section>")
    print
} else {
    print
}
}' index.html
