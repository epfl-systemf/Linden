#!/usr/bin/env bash
# Install artifact dependencies and files in current folder
# Must be run in the folder that contains provision.sh

set -e

if [ "$VERBOSE" = "1" ]; then
    set -x
fi

PACKAGES=(
    # Basics
    build-essential pkg-config make autoconf automake m4 rsync
    # VirtualBox guest additions dependencies
    gcc perl
    # OCaml
    opam
    # Utilities
    git curl
    # Warblre dependency
    libgmp-dev
    # Emacs
    emacs
)

loud() {
    local msg=$*; local blue="\e[1;34m"; local reset="\e[0m";
    local sep="${blue}$(printf "%${#msg}s" | tr " " "${msg:0:1}")${reset}"
    printf "${sep}\n${blue}%s${reset}\n${sep}\n" "$msg"
}

loud $(pwd)
loud $(ls ~/Desktop/)

#############################################
loud "= Confirm that artifact is available ="
#############################################

cd Desktop/artifact

###########################################
loud "= Install required system packages ="
###########################################

sudo DEBIAN_FRONTEND=noninteractive \
     apt-get -y install "${PACKAGES[@]}"

git config --global user.name "User"
git config --global user.email "user@example.com"

##########################################
loud "= Install dependencies using OPAM ="
##########################################

opam init --yes --auto-setup
opam switch --no-install create .
opam pin -y add warblre https://github.com/epfl-systemf/Warblre.git#a1ffc3f2e47d942ad9e1194dfb71f0783ead6d8a
eval $(opam env)

###########################
loud "= Build Coq proofs ="
###########################

dune build

############################################
loud "= Install VS Code with VSCoq Legacy ="
############################################

cd ../
wget -O code.deb "https://code.visualstudio.com/sha/download?build=stable&os=linux-deb-x64"
sudo DEBIAN_FRONTEND=noninteractive apt install -y ./code.deb
rm code.deb
#code --install-extension coq-community.vscoq1 # does not work...
# wget --compression=auto -O vscoq.vsix https://marketplace.visualstudio.com/_apis/public/gallery/publishers/coq-community/vsextensions/vscoq1/latest/vspackage # from VS Code marketplace
wget --compression=auto -O vscoq.vsix https://open-vsx.org/api/coq-community/vscoq1/0.5.0/file/coq-community.vscoq1-0.5.0.vsix # from open-vsx
code --install-extension vscoq.vsix

################################################
loud "= Install Proof General and company-coq ="
################################################

cat > ~/.emacs <<EOF
(require 'package)
;; (setq gnutls-algorithm-priority "NORMAL:-VERS-TLS1.3") ; see remark below
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(package-initialize)
EOF
emacs --batch --eval "(progn (require 'package) (add-to-list 'package-archives '(\"melpa\" . \"https://melpa.org/packages/\") t) (package-refresh-contents) (package-install 'proof-general) (package-install 'company-coq))"

loud "= Setup complete ="
#########################
