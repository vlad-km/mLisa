;;; -*- mode:lisp; coding:utf-8 -*-

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)


(eval-when (:compile-toplevel :load-toplevel :execute)
  (unless (find-package :lilu)
    (make-package :lilu :use (list 'cl)))
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

(defun assert-error (form datum &rest args)
  (error
   (if datum
       (jscl::%%coerce-condition 'simple-error datum args)
		 (make-condition 'simple-error
				             :format-control "Assert failed: ~s."
				             :format-arguments (list form)))))

(defmacro assert (test &optional ignore datum &rest args)
  (let ((value (gensym "ASSERT-VALUE"))
        (name (gensym "ASSERT-BLOCK")))
    `(block
         ,name
       (let ((,value ,test))
         (when (not ,value)
           (assert-error ',test ,datum ,@args))))))


;;; EOF
