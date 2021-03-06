﻿// -*- mode: c++; c-file-style: "linux"; c-basic-offset: 2; indent-tabs-mode: nil -*-
//
//  Copyright (C) 2004-2015 Andrej Vodopivec <andrej.vodopivec@gmail.com>
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

/*!\file 
This file declares everything needed in order to style all the elements
shown on the work sheet.
*/


#ifndef TEXTSTYLE_H
#define TEXTSTYLE_H

#include <wx/colour.h>
#include <wx/font.h>
#include <wx/config.h>

//! A text style for the work sheet
class Style
{
public:
  //! The constructor
  Style()
  {
    m_bold = false;
    m_italic = false;
    m_underlined = false;
    m_fontSize = 10;
  };
  //! Read thisstyle from a config source
  void Read(wxConfigBase *config, wxString where);
  //! Write this style to a config source
  void Write(wxConfigBase *config, wxString where);
  //! Set this style
  void Set(wxString name,
           wxColor color,
           bool bold = false, bool italic = false, bool underlined = false,
           int fontSize=10)
    {
      m_name = name;
      m_color = color;
      m_bold = bold;
      m_italic = italic;
      m_underlined = underlined;
      m_fontSize = fontSize;
    }
  //! Is this style italic?
  bool Italic(){return m_italic;}
  //! Make this style italic
  void Italic(bool italic){m_italic = italic;}
  //! Is this style bold?
  bool Bold(){return m_bold;}
  //! Make this style bold
  void Bold(bool bold){m_bold = bold;}
  //! Is this style underlined?
  bool Underlined(){return m_underlined;}
  //! Make this style underlined
  void Underlined(bool underlined){m_underlined = underlined;}
  //! The font size of this style
  int FontSize(){return m_fontSize;}
  //! Set the font size of this style
  void FontSize(int size){m_fontSize = size;}
  //! The font name of this style
  wxString FontName(){return m_fontName;}
  //! Set the font name of this style
  void FontName(wxString name){m_fontName = name;}
  //! Get the color of this style
  wxColor GetColor(){return m_color;}
  //! Set the color of this style
  wxString Name(){return m_name;}
  //! Set the color of this style
  void Color(wxColor color){m_color = color;}
  //! Set the color of this style
  void Color(int r, int g, int b){m_color = wxColor(r,g,b);}
  //! Get the color of this style
  wxColor Color(){return m_color;}
private:
  wxColor m_color;
  wxString m_fontName;
  wxString m_name;
  int m_fontSize;
  bool m_bold;
  bool m_italic;
  bool m_underlined;
};

/*! All text styles known to wxMaxima

  \attention If this list is changed the config dialogue 
  sometimes needs additional tweaking after that.
 */
enum TextStyle
{
  TS_DEFAULT = 0,
  TS_VARIABLE,
  TS_NUMBER,
  TS_FUNCTION,
  TS_SPECIAL_CONSTANT,
  TS_GREEK_CONSTANT,
  TS_STRING,
  TS_INPUT,
  TS_MAIN_PROMPT,
  TS_OTHER_PROMPT,
  TS_LABEL,
  TS_USERLABEL,
  TS_HIGHLIGHT,
  TS_WARNING,
  TS_ERROR,
  TS_TEXT,
  TS_HEADING6,
  TS_HEADING5,
  TS_SUBSUBSECTION,
  TS_SUBSECTION,
  TS_SECTION,
  TS_TITLE,
  TS_TEXT_BACKGROUND,
  TS_DOCUMENT_BACKGROUND,
  TS_CELL_BRACKET,
  TS_ACTIVE_CELL_BRACKET,
  TS_CURSOR,
  TS_SELECTION,
  TS_EQUALSSELECTION,
  TS_OUTDATED,
  TS_CODE_VARIABLE,
  TS_CODE_FUNCTION,
  TS_CODE_COMMENT,
  TS_CODE_NUMBER,
  TS_CODE_STRING,
  TS_CODE_OPERATOR,
  TS_CODE_ENDOFLINE,
  NUMBEROFSTYLES //!< This is no style, but its number tells us how many styles we defined
};

#endif // TEXTSTYLE_H
