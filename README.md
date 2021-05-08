## mLisa
## Lisp production-rule system (LISA) modified for JSCL.
## A fork of `http://lisa.sourceforge.net/`. Fossil Lisp code, ancient as mammoth's shit

#### Compilation only under web-repl (platform Electron)
```lisp
(setq bin #())
(load "00-prelude.lisp" :hook bin)
(load "01-utils.lisp" :hook bin)
(load "02-belief.lisp" :hook bin)
(load "03-reflect.lisp" :hook bin)
(load "04-core.lisp" :hook bin)
(load "05-rete.lisp" :hook bin)
(load "06-config.lisp" :hook bin :output "mlisa.js")
```
Will be bundle js-code "mlisa.js".

##### as is, without any guarantees or obligations
