#!/bin/bash
set -eu

blue=$(tput setaf 4 || echo)
bold=$(tput bold || echo)
gray=$(tput setaf 7 || echo)
reset=$(tput sgr0 || echo)

info() {
  echo -e "${blue}$1${reset}" 1>&2
}

dir="$1"

export STARSHIP_CONFIG=/tmp/demo-starship.toml

cat > "$STARSHIP_CONFIG" <<EOF
add_newline=false

[cmd_duration]
disabled = true

[username]
disabled = true

[hostname]
disabled = true

[perl]
disabled = true
EOF

prompt() {
    starship prompt
    echo "$@"
}

comment() {
    echo -e "# ${bold}${gray}$1${reset}"
}

_ls() {
    # this has to be passed with env for some reason
    env COLUMNS=80 exa --color=always --time-style=long-iso "$@"
}

_ll() {
    _ls -l "$@"
}

cd "$dir"

comment "clone xv6 repo and compile it"

prompt "git clone \$XV6_PATH xv6"
git clone --quiet "$XV6_PATH" xv6
cd xv6

prompt "ls"
_ls

prompt "make"
make --quiet 2>/dev/null

prompt "ls"
_ls

echo
comment "get the total space used in the file system"

prompt "df -h ."
df -h .

echo
comment "the repo appears larger than the space used..."

prompt "du -sh ."
du -sh .

comment "...because some of the files are sparse"

prompt "ls -l initcode"
_ll initcode

prompt "hexdump initcode"
hexdump initcode

# confirms that initcode and xv6.img are the sparse files
# prompt "rm initcode xv6.img"
# rm initcode xv6.img
#
# prompt "df -h .; du -sh ."
# df -h .
# du -sh .

echo
comment "create a small number of files and inspect them"

cd ..
prompt "touch foo; mkdir bar; echo 'hello' > baz"
touch foo; mkdir bar; echo "hello" > baz

prompt "ls -l"
_ll

echo
comment "clean up the system"
prompt "rm -r xv6"
rm -r xv6

sleep 1

comment "check that space was recovered"
prompt "df -h ."
df -h .

# cleanup
rm -r bar
rm foo baz
