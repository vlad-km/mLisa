;;; -*- mode:lisp; coding:utf-8 -*-

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)


(eval-when (:compile-toplevel :load-toplevel :execute)
  (unless (find-package :lilu)
    (make-package :liu :use (list 'cl)))
  (unless (find-package :lisa)
    (make-package :lisa :use (list 'cl)))
  (unless (find-package :lisa-user)
    (make-package :lisa-user :use (list 'cl)))
  (unless (find-package :reflect)
    (make-package :reflect :use (list 'cl)))
  (unless (find-package :belief)
    (make-package :belief :use (list 'cl)))
  (unless (find-package :heap)
    (make-package :heap :use (list 'cl))))



;;; EOF
