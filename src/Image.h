﻿// -*- mode: c++; c-file-style: "linux"; c-basic-offset: 2; indent-tabs-mode: nil -*-
//
//  Copyright (C) 2004-2015 Andrej Vodopivec <andrej.vodopivec@gmail.com>
//            (C) 2014-2015 Gunter Königsmann <wxMaxima@physikbuch.de>
//
//  This program is free software; you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation; either version 2 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//
//  You should have received a copy of the GNU General Public License
//  along with this program; if not, write to the Free Software
//  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//
//  SPDX-License-Identifier: GPL-2.0+

/*! \file
  This file declares the class Image

  Image stores compressed images and handles scaling and uncompressing them.
*/

#ifndef IMAGE_H
#define IMAGE_H

#include "Cell.h"
#include <wx/image.h>

#include <wx/filesys.h>
#include <wx/fs_arc.h>
#include <wx/buffer.h>

/*! Manages an auto-scaling image

  This class keeps two versions of an image:
    - The image in its original compressed format. This way the image can losslessly
      be exported lateron
    - A bitmap version of the image that is scaled down to a size that makes sense 
      with the current viewport.

  Storing images this way has many advantages:
    - It allows us to restrict scaling operations to only once on actually drawing 
      the image after a resize of the wxMaxima window.
    - We can keep (and therefore export and save) jpeg photos in their original 
      format instead of using the .png compression that is superior for line art - 
      but not for depicting real-live images.
    - We save time on saving the .wxmx file since image compression, if done good, 
      might need a good deal of time and this class never needs to compress images
      itself.
    - It allows images to keep their metadata, if needed
    - and if we have big images (big plots or for example photographs) we don't need
      to store them in their uncompressed form.
    - One could even delete the cached scaled images for all cells that currently 
      are off-screen in order to save memory.
 */
class Image
{
public:
  //! A constructor that generates an empty image. See LoadImage()
  Image(Configuration **config);

  //! A constructor that loads the compressed file from a wxMemoryBuffer
  Image(Configuration **config, wxMemoryBuffer image, wxString type);

  /*! A constructor that loads a bitmap

    This constructor actually has to do some compression since we got
    the bitmap in an uncompressed form.
   */
  Image(Configuration **config, const wxBitmap &bitmap);

  /*! A constructor that loads an image

    \param config The pointer to the current configuration storage for the worksheet
    \param image The name of the file
    \param filesystem The filesystem to load it from
    \param remove true = Delete the file after loading it
   */
  Image(Configuration **config, wxString image, bool remove = true, wxFileSystem *filesystem = NULL);

  ~Image();

  /*! Sets the name of the gnuplot source and data file of this image

    Causes the files to be cached if they are not way too long; As the files
    are text-only they profit from being compressed and are stored in the 
    memory in their compressed form.
   */
  void GnuplotSource(wxString gnuplotFilename, wxString dataFilename, wxFileSystem *filesystem = NULL);
  /*! Returns the gnuplot source file name of this image

    If maxima has deleted the temporary file in the meantime or if it comes from 
    a .wxmx file and has never been created from maxima the file is created by this 
    function.

    If the file cannot be created (for example if no gnuplot source exists/ 
    is known) this function returns wxEmptyString.
   */
  wxString GnuplotSource();
  /*! Returns the gnuplot data file name of this image

    If maxima has deleted the temporary file in the meantime or if it comes from 
    a .wxmx file and has never been created from maxima the file is created by this 
    function.

    If the file cannot be created (for example if no gnuplot source exists/ 
    is known) this function returns wxEmptyString.
   */
  wxString GnuplotData();

  //! Returns the gnuplot source of this image
  wxMemoryBuffer GetGnuplotSource();
  //! Returns the gnuplot data of this image
  wxMemoryBuffer GetGnuplotData();
  
  /*! Temporarily forget the scaled image in order to save memory

    Will recreate the scaled image as soon as needed.
   */
  void ClearCache()
  { if ((m_scaledBitmap.GetWidth() > 1) || (m_scaledBitmap.GetHeight() > 1))m_scaledBitmap.Create(1, 1); }

  //! Reads the compressed image into a memory buffer
  wxMemoryBuffer ReadCompressedImage(wxInputStream *data);

  //! Returns the file name extension of the current image
  wxString GetExtension()
  { return m_extension; };

  //! Loads an image from a file
  void LoadImage(wxString image, bool remove = true, wxFileSystem *filesystem = NULL);

  //! The maximum width this image shall be displayed with
  double GetMaxWidth(){return m_maxWidth;}
  //! The maximum height this image shall be displayed with
  double GetMaxHeight(){return m_maxHeight;}
  //! Set the maximum width this image shall be displayed with
  void   SetMaxWidth(double width){m_maxWidth = width;}
  //! Set the maximum height this image shall be displayed with
  void   SetMaxHeight(double height){m_maxHeight = height;}
  
  //! "Loads" an image from a bitmap
  void LoadImage(const wxBitmap &bitmap);

  //! Saves the image in its original form, or as .png if it originates in a bitmap
  wxSize ToImageFile(wxString filename);

  //! Returns the bitmap being displayed with custom scale
  wxBitmap GetBitmap(double scale = 1.0);

  //! Does the image show an actual image or an "broken image" symbol?
  bool IsOk() {return m_isOk;}
  
  //! Returns the image in its unscaled form
  wxBitmap GetUnscaledBitmap();

  //! Can be called to specify a specific scale
  void Recalculate(double scale = 1.0);

  //! The width of the scaled image
  long m_width;
  //! The height of the scaled image
  long m_height;

  //! Returns the original image in its compressed form
  wxMemoryBuffer GetCompressedImage()
  { return m_compressedImage; }

  //! Returns the original width
  size_t GetOriginalWidth()
  { return m_originalWidth; }

  //! Returns the original height
  size_t GetOriginalHeight()
  { return m_originalHeight; }

  //! The image in its original compressed form
  wxMemoryBuffer m_compressedImage;

protected:
  //! A zipped version of the gnuplot commands that produced this image.
  wxMemoryBuffer m_gnuplotSource_Compressed;
  //! A zipped version of the gnuplot data needed in order to create this image.
  wxMemoryBuffer m_gnuplotData_Compressed;
  //! The width of the unscaled image
  size_t m_originalWidth;
  //! The height of the unscaled image
  size_t m_originalHeight;
  //! The bitmap, scaled down to the screen size
  wxBitmap m_scaledBitmap;
  //! The file extension for the current image type
  wxString m_extension;
  //! Does this image contain an actual image?
  bool m_isOk;
  //! The gnuplot source file for this image, if any.
  wxString m_gnuplotSource;
  //! The gnuplot data file for this image, if any.
  wxString m_gnuplotData;
private:
  Configuration **m_configuration;
  //! The upper width limit for displaying this image
  double m_maxWidth;
  //! The upper height limit for displaying this image
  double m_maxHeight;
  //! The name of the image, if known.
  wxString m_imageName;
};

#endif // IMAGE_H
