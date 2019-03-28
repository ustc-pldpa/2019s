
# Coq + Proof General + Emacs on Windows

## 1. Coq
[Coq](https://coq.inria.fr/) is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs.

(1) Download the pre-built packages of the [latest release](https://github.com/coq/coq/releases/latest), and install it. As an example, my installation directory is "D:\Coq".

(2) Add the installation directory (in my case "D:\Coq\bin") to the system environment “Path”.

## 2. Proof General
[Proof General](https://proofgeneral.github.io/) is a generic interface for proof assistants (also known as interactive theorem provers), based on the extensible, customizable text editor [Emacs](https://www.gnu.org/software/emacs/).

(1) Download Proof General (the zip package) at <https://github.com/ProofGeneral/PG>

(2) Unzip the package in your installation directory. As an example, I put it at "D:\PG".

## 3. Emacs

[Emacs](https://www.gnu.org/software/emacs/) is an extensible, customizable, self-documenting real-time display editor.

(1) Download [Emacs for windows](http://mirrors.nju.edu.cn/gnu/emacs/windows/)

(2) Run emacs after installation, and do some random change of options in the "Options" menu and then press "Save options". This will generate ".emacs" in your HOME directory. For me on Windows 7 (or 10), as an example, the generated .emacs is found at `C:\users\userID\AppData\Roaming`.

(3) Add the following line to the .emacs file (change the directory to your own installation directory for proof general):
```
(load -file "d:\PG\generic\proof-site.el")
```
