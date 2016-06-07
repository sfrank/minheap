;;;; MINHEAP is by Stephan Frank <defclass@googlemail.com>, 2007-2012.
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included
;;;; in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(defpackage :splay-heap (:use :cl)
  (:export
   #:pairing-heap
   #:clear-heap
   #:empty-p
   #:insert
   #:peek-min
   #:extract-min
   #:extract-node
   #:heap-size
   #:decrease-key
   #:meld
   #:node-find
   ))

(in-package :splay-heap)

;;; splay tree functions

(defstruct splay-node
  (segment nil :type (or fixnum null))
  (element nil)
  (left nil :type (or null splay-node))
  (right nil :type (or null splay-node)))

(declaim (inline segment<))
(defun segment< (a b)
  (declare (type (or null fixnum) a b)
	   (optimize (speed 3) (space 0) (debug 0) (safety 0)))
  (cond
    ((null b)
     nil)
    ((null a)
     t)
    (t
     (< (the fixnum a) (the fixnum b)))))

(declaim (inline segment>))
(defun segment> (a b)
  (declare (type (or null fixnum) a b)
	   (optimize (speed 3) (space 0) (debug 0) (safety 0)))
  (cond
    ((null a)
     nil)
    ((null b)
     t)
    (t
     (> (the fixnum a) (the fixnum b)))))

(defun splay-tree-splay (tree segment)
  (declare (optimize (speed 3) (space 0) (debug 0) (safety 0)))
  (when tree
    (let ((middle (make-splay-node :left nil :right nil)))
      (declare (dynamic-extent middle))
      (let ((left middle)
            (right middle)
	    tmp)
        (loop for cur-seg  = (splay-node-segment tree)
              while (and cur-seg
			 (/= (the fixnum segment) cur-seg))
              do
              (cond
                ((segment< segment cur-seg)
                 (when (and (splay-node-left tree)
                            (segment< segment (splay-node-segment
					       (splay-node-left tree))))
                   (setf tmp (splay-node-left tree)
                         (splay-node-left tree) (splay-node-right tmp)
                         (splay-node-right tmp) tree
                         tree tmp))
                 (unless (splay-node-left tree)
                   (return))
                 (setf (splay-node-left right) tree
                       right tree
                       tree (splay-node-left tree)))
                (t
                 (when (and (splay-node-right tree)
                            (segment> segment (splay-node-segment
					(splay-node-right tree))))
                   (setf tmp (splay-node-right tree)
                         (splay-node-right tree) (splay-node-left tmp)
                         (splay-node-left tmp) tree
                         tree tmp))
                 (unless (splay-node-right tree)
                   (return))
                 (setf (splay-node-right left) tree
                       left tree
                       tree (splay-node-right tree)))))
        (setf (splay-node-right left) (splay-node-left tree)
              (splay-node-left right) (splay-node-right tree)
              (splay-node-left tree) (splay-node-right middle)
              (splay-node-right tree) (splay-node-left middle))
        tree))))

(defun splay-tree-insert (tree segment element &optional (overwrite nil))
  (declare (optimize (speed 3) (space 0) (debug 0) (safety 0)))
  (let ((new (make-splay-node :segment segment :element element)))
    (if (null tree)
        (values new t)
        (let ((tree (splay-tree-splay tree segment)))
          (cond
            ((segment< segment (splay-node-segment tree))
             (setf (splay-node-left new) (splay-node-left tree)
                   (splay-node-right new) tree
                   (splay-node-left tree) nil)
             (values new t))
            ((segment> segment (splay-node-segment tree))
             (setf (splay-node-right new) (splay-node-right tree)
                   (splay-node-left new) tree
                   (splay-node-right tree) nil)
             (values new t))
            (t
             (when overwrite
	       (setf (splay-node-element tree) element))
             (values tree nil)))))))

(defun splay-tree-delete (tree segment)
  (declare (optimize (speed 3) (space 0) (debug 0) (safety 0)))
  (when tree
    (let ((tree (splay-tree-splay tree segment)))
      (cond
        ((= (the fixnum segment) (the fixnum (splay-node-segment tree)))
         (if (null (splay-node-left tree))
             (values (splay-node-right tree) t)
             (let ((result (splay-tree-splay (splay-node-left tree) segment)))
               (setf (splay-node-right result) (splay-node-right tree))
               (values result t))))
        (t
         (values tree nil))))))

;;; heap functions
(defclass splay-heap ()
  ((tree :initform nil :type (or splay-node null))
   (size :initform 0 :type fixnum)))

(defun insert (heap key item)
  (multiple-value-bind (tree new-node)
      (splay-tree-insert (slot-value heap 'tree) key item)
    (when new-node
      (incf (slot-value heap 'size)))
    (setf (slot-value heap 'tree) tree)
    new-node))

(defun extract-min (heap)
  (let ((tree (splay-tree-splay (slot-value heap 'tree)
				most-negative-fixnum)))
    (when tree
      (decf (slot-value heap 'size))
      (setf (slot-value heap 'tree)
        (splay-tree-delete heap (splay-node-segment tree)))
      (values (splay-node-element tree)
              (splay-node-segment tree)))))

;; TODO, change parameter types to the same as other heaps
(defun extract-node (heap key)
  (let ((tree (splay-tree-splay (slot-value heap 'tree) key)))
    (when (and tree
               (= key (splay-node-segment tree)))
      (multiple-value-bind (result deleted)
          (splay-tree-delete tree key)
        (setf (slot-value heap 'tree) result)
        (when deleted
          (decf (slot-value heap 'size))
          (values (splay-node-element tree)
                  (splay-node-segment tree)))))))
    
(defun node-find (heap key)
  (when (slot-value heap 'tree)
    (let ((tree (splay-tree-splay (slot-value heap 'tree) key)))
      (setf (slot-value heap 'tree) tree)
      (when (= key (splay-node-segment tree))
        (splay-node-element tree)))))

(defun peek-min (heap)
  (when (not (empty-p heap))
    (let ((tree (setf (slot-value heap 'tree)
		      (splay-tree-splay (slot-value heap 'tree)
					most-negative-fixnum))))
      (values (splay-node-element tree)
              (splay-node-segment tree)))))

(defun heap-size (heap)
  (slot-value heap 'size))

(defun empty-p (heap)
  (zerop (slot-value heap 'size)))

(defun clear-heap (heap)
  (setf (slot-value heap 'size) 0
        (slot-value heap 'tree) nil))
