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

(defun equalp (x y)
  (typecase x
    (number (and (numberp y) (= x y)))
    (character (and (characterp y) (char-equal x y)))
    (cons (and (consp y)
               (equalp (car x) (car y))
               (equalp (cdr x) (cdr y))))
    (vector (and (vectorp y)
                 (let ((lx (length x)))
                   (= lx (length y))
                   (dotimes (i lx t)
                     (when (not (equalp (aref x i) (aref y i)))
                       (return nil))))))
    (array (and (arrayp y)
                (equalp (array-dimensions x) (array-dimensions y))
                (dotimes (i (length x) t)
                  (when (not (equalp (aref x i) (aref y i)))
                    (return nil)))))
    (hash-table
     (and (hash-table-p y)
          (eql (hash-table-count x)(hash-table-count y))
          (eql (hash-table-test x)(hash-table-test y))
          (block nil
            (if (= (hash-table-count x) 0)
                t
              (maphash (lambda (k v)
                         (multiple-value-bind (other-v presentp)
                             (gethash k y)
                           (when (or (not presentp)
                                     (not (equalp v other-v)))
                             (return nil))))
                       x)
              t))))
    (t (equal x y))))


;;; EOF
