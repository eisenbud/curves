% This is msribib.bst
% $Revision: 1.15 $
% $Date: 2000/02/25 04:50:52 $
%
% This file is derived from chicago.bst by Glenn Pauley.  It is called
% msribib.bst and was developed by Silvio Levy for the book series
% Mathematical Sciences Research Insitute Publications.  It follows the
% Chicago Manual of Style in using author and year as the bib key.
%
% Place this file in the BibTeX search path.
% You need to say \usepackage{msribib} in your latex document. You
% should have received the files msribib.sty and url.sty together with
% this one.
%
% Usage:
%
% \cite{key}       gives        [author-last-name year]
% \citeyear{key}   gives        [year]
% \citeNP{key}     gives        author-last-name year
% \citeyearNP{key} gives        year
%
% Simple example:
%
% For details, see \cite{foo,bar}
%
% gives [Foote 1993; Barlow 1994]
%
% Complicated examples:  
%
% See [\citeNP[p.~666]{foo}; \citeNP{bar}]
%
% gives [Foote 1993, p.~666; Barlow 1994]
%
% It was proved in [\citeNP{Paper1bySoAndSo}; \citeyearNP{Paper1bySoAndSo}]
%
% gives [SoAndSo 1993; 1994]
%
%   Reference list ordering: alphabetical by author or whatever passes
%    for author in the absence of one.
%

ENTRY
  { address
    author
    booktitle
    chapter
    description
    edition
    editor
    howpublished
    institution
    journal
    key
    month
    note
    number
    organization
    pages
    publisher
    school
    series
    subyear
    title
    type
    url
    venue
    volume
    year
  }
  {}
  { label.year extra.label sort.year sort.label }

INTEGERS { output.state before.all mid.sentence after.sentence after.block novon}

FUNCTION {init.state.consts}
{ #0 'before.all :=
  #1 'mid.sentence :=
  #2 'after.sentence :=
  #3 'after.block :=
}

STRINGS { s t u v }

FUNCTION {output.nonnull}
{ 's :=
  output.state mid.sentence =
    { ", " * write$ }
    { output.state after.block =
%% SL: blocks separated by comma instead of period; no \newblock.
    { 
%      add.period$ write$
      ", " * write$
      newline$
%      "\newblock " write$
    }
    { output.state before.all =
        'write$
        { add.period$ " " * write$ }
      if$
    }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

% Use a colon to separate output. Used only for address/publisher
% combination in book/inbook types, address/institution for manuals,
% and organization:publisher for proceedings (inproceedings).
%
FUNCTION {output.nonnull.colon}
{ 's :=
  output.state mid.sentence =
    { ": " * write$ }
    { output.state after.block =
%% SL: blocks separated by comma instead of period; no \newblock.
    { 
%      add.period$ write$
      ", " * write$
      newline$
%      "\newblock " write$
    }
    { output.state before.all =
        'write$
        { add.period$ " " * write$ }
      if$
    }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnull
  if$
}

FUNCTION {output.colon}
{ duplicate$ empty$
    'pop$
    'output.nonnull.colon
  if$
}

FUNCTION {output.check}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnull
  if$
}

FUNCTION {output.check.colon}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnull.colon
  if$
}

FUNCTION {output.yearnopar.check}
{ year empty$
     { "empty year in " cite$ * warning$ }
     { write$
        ", " 
% SL: switch order of month and year
       month empty$
          { }
          { month * " " *}
       if$
       year *
       mid.sentence 'output.state :=
     }
  if$
}

FUNCTION {year.check}
{ year empty$
     { "empty year in " cite$ * warning$ "" } %place null string on stack
     { 
        " (" 
% SL: switch order of month and year
       month empty$
          { }
          { month * " " *}
       if$
% remove extra label from year
       year * ")" * %extra.label *
       mid.sentence 'output.state :=
     }
  if$
}

FUNCTION {new.block}
{ output.state before.all =
    'skip$
    { after.block 'output.state := }
  if$
}

FUNCTION {new.sentence}
{ output.state after.block =
    'skip$
    { output.state before.all =
    'skip$
    { after.sentence 'output.state := }
      if$
    }
  if$
}

FUNCTION {url.output}
{ url empty$
    {}
    {"\urlhook {" url * "} \posturlhook" * output.nonnull}
  if$
}

FUNCTION {desc.output}
{ description empty$
    {}
    {"\descriptionhook{" description * "}" * output.nonnull}
  if$
}

FUNCTION {fin.entry}
{
  new.sentence
  url.output
  new.sentence
  note output
  new.sentence
  desc.output
  add.period$
  write$
  newline$
}

FUNCTION {not}
{   { #0 }
    { #1 }
  if$
}

FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$
}

FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$
}

FUNCTION {new.block.checka}
{ empty$
    'skip$
    'new.block
  if$
}

FUNCTION {new.block.checkb}
{ empty$
  swap$ empty$
  and
    'skip$
    'new.block
  if$
}

FUNCTION {new.sentence.checka}
{ empty$
    'skip$
    'new.sentence
  if$
}

FUNCTION {new.sentence.checkb}
{ empty$
  swap$ empty$
  and
    'skip$
    'new.sentence
  if$
}

FUNCTION {field.or.hook}
{ duplicate$ empty$
    { pop$ "\noyearhook " }
    'skip$
  if$
}

FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$
}

% SL: Embolden the top string on the stack.
%
FUNCTION {embolden}
{ duplicate$ empty$
    { pop$ "" }
    { "{\bf " swap$ * "}" * }
  if$
}

%
% Emphasize the top string on the stack.
%
FUNCTION {emphasize}
{ duplicate$ empty$
    { pop$ "" }
    { "{\em " swap$ * "}" * }
  if$
}

% SL: Embolden the top string on the stack, but add a trailing space.
%
FUNCTION {embolden.space}
{ duplicate$ empty$
    { pop$ "" }
    { "{\bf " swap$ * "\/}" * }
  if$
}

%
% Emphasize the top string on the stack, but add a trailing space.
%
FUNCTION {emphasize.space}
{ duplicate$ empty$
    { pop$ "" }
    { "{\em " swap$ * "\/}" * }
  if$
}

INTEGERS { nameptr namesleft numnames }
%
% [SL: all authors are now first+last.]
% Format bibliographical entries with the first author last name first,
% and subsequent authors with initials followed by last name.
% All names are formatted in this routine.
%
FUNCTION {format.names}
{ 's :=
  #1 'nameptr :=               % nameptr = 1;
  s num.names$ 'numnames :=    % numnames = num.name$(s);
  numnames 'namesleft :=
    { namesleft #0 > }

    { nameptr #1 =
%        {s nameptr "{vv~}{ll}{, jj}{, f.}" format.name$ 't := }
        {s nameptr "{f. }{vv~}{ll}{, jj}" format.name$ 't := }
        {s nameptr "{f. }{vv~}{ll}{, jj}" format.name$ 't := }
      if$
      nameptr #1 >
        { namesleft #1 >
              { ", " * t * }
              { numnames #2 >
                  { "\serialcomma" * }
                  'skip$
                if$
                t "others" =
                    { " et~al." * }
                    { " \andword{} " * t * } % from Chicago Manual of Style
                  if$
               }
               if$
             }
            't
        if$
        nameptr #1 + 'nameptr :=          % nameptr += 1;
        namesleft #1 - 'namesleft :=      % namesleft =- 1;
    }
  while$
}

FUNCTION {format.names.fml}
%
% Format names in "familiar" format, with first initial followed by
% last name. Like format.names, ALL names are formatted.
%
{ 's :=
  #1 'nameptr :=               % nameptr = 1;
  s num.names$ 'numnames :=    % numnames = num.name$(s);
  numnames 'namesleft :=
  namesleft #2 > 
  { s nameptr "{f. }{vv~}{ll}{, jj}" format.name$ " et~al." * }
  {
    { namesleft #0 > }

    { s nameptr "{f. }{vv~}{ll}{, jj}" format.name$ 't :=

      nameptr #1 >
        { namesleft #1 >
              { ", " * t * }
               { numnames #2 >
                    { "\serialcomma" * }
                    'skip$
                  if$
                  t "others" =
                        { " et~al." * }
                        { " \andword{} " * t * }
                      if$
                }
               if$
             }
            't
        if$
        nameptr #1 + 'nameptr :=          % nameptr += 1;
        namesleft #1 - 'namesleft :=      % namesleft =- 1;
    }
  while$
  }
  if$
}

FUNCTION {format.authors}
{ author empty$
    { "" }
    { author format.names }
  if$
}

FUNCTION {format.key}
{ empty$
    { key field.or.null }
    { "" }
  if$
}

%
% Format editor names for use in the "in" types: inbook, incollection,
% inproceedings: first initial, then last names. When editors are the
% LABEL for an entry, then format.editor is used which lists editors
% by last name first.
%
FUNCTION {format.editors.fml}
{ editor empty$
    { "" }
    { editor format.names.fml
% SL: remove the "Ed"
%      editor num.names$ #1 >
%    { " (Eds.)" * }
%    { " (Ed.)" * }
%      if$
    }
  if$
}

%
% Format editor names for use in labels, last names first.
%
FUNCTION {format.editors}
{ editor empty$
    { "" }
    { editor format.names
      editor num.names$ #1 >
% SL: expanded Eds. to "editors"
    { " (editors)" * }
    { " (editor)" * }
      if$
    }
  if$
}


FUNCTION {format.title}
{ title empty$
    { "" }
    { "``" title * "''" * }
%% SL: no decapitalization, and use quotation marks.
%    { title "t" change.case$ }
  if$
}

FUNCTION {n.dashify}
{ 't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "-" =
    { t #1 #2 substring$ "--" = not
        { "--" *
          t #2 global.max$ substring$ 't :=
        }
        {   { t #1 #1 substring$ "-" = }
        { "-" *
          t #2 global.max$ substring$ 't :=
        }
          while$
        }
      if$
    }
    { t #1 #1 substring$ *
      t #2 global.max$ substring$ 't :=
    }
      if$
    }
  while$
}

FUNCTION {tie.or.space.connect}
{ duplicate$ text.length$ #3 <
    { "~" }
    { " " }
  if$
  swap$ * *
}

FUNCTION {format.btitle}
{ 
  title emphasize 
  venue empty$
    { }
    { " (" venue ")"  * * *
  }
  if$
  volume empty$
    {  }
    { 
      ", " * type empty$ {"vol."} {type} if$ * volume tie.or.space.connect 
    }
  if$
  edition empty$
    { }
    { ", " * edition * " \editionword{}" * }
  if$
}

FUNCTION {format.emphasize.booktitle}
{ edition empty$
  { booktitle emphasize }
  { booktitle empty$
    { booktitle emphasize }
    { "{\em " booktitle * "}, " * edition * " \editionword{}" *}
    if$
    }
  if$
  }


FUNCTION {either.or.check}
{ empty$
    'pop$
    { "can't use both " swap$ * " fields in " * cite$ * warning$ }
  if$
}

FUNCTION {format.bvolume}
{ volume empty$
    {  }
    { 
      ", " * type empty$ {"vol."} {type} if$ * volume tie.or.space.connect
      series empty$
        {"volume and number" number either.or.check}
        {number empty$
        {"volume in " cite$ " should probably be (series) number" * * warning$}
        'skip$
        if$}
      if$
    }
  if$
}

FUNCTION {format.number.series}
{
      number empty$
    { series field.or.null }
    { 
      series empty$
        { "there's a number but no series in " cite$ * warning$ }
        { series " {\bf " * number * "}" * }
      if$
    }
      if$
}

INTEGERS { multiresult }

FUNCTION {multi.page.check}
{ 't :=
  #0 'multiresult :=
    { multiresult not
      t empty$ not
      and
    }
    { t #1 #1 substring$
      duplicate$ "-" =
      swap$ duplicate$ "," =
      swap$ "+" =
      or or
    { #1 'multiresult := }
    { t #2 global.max$ substring$ 't := }
      if$
    }
  while$
  multiresult
}

FUNCTION {format.pages}
{ pages empty$
  { "" }
  { pages multi.page.check
	{ "pp.\ " pages n.dashify tie.or.space.connect } % gnp - removed ()
	{ "pp.\ " pages tie.or.space.connect }
    if$
  }
  if$
}

% By Young (and Spencer)
% GNP - fixed bugs with missing volume, number, and/or pages
%
% Format journal, volume, number, pages for article types.
%
FUNCTION {format.jour.vol}
{ journal empty$
    { "no journal in " cite$ * warning$
      "" }
    { journal emphasize.space }
    if$
  number empty$
    { volume empty$
       { "no number and no volume in " cite$ * warning$
         "" * }
% SL: volume in bold not \em; no tie
       { " {\bf " * volume * "}" * }
      if$
    }
    { volume empty$
      {"no volume for " cite$ * warning$
       "no.\ " * number * }
      { " " *
% SL: volume in bold not \em; no tie
        volume embolden.space
        ":" * number * * }
      if$
    }
  if$
  year.check *
  pages empty$
    {"page numbers missing in " cite$ * warning$
     "" * } % gnp - place a null string on the stack for output
    { duplicate$ empty$
      { pop$ format.pages }
      { ", " *  pages n.dashify * } % gnp - removed pp. for articles
      if$
    }
  if$
}

FUNCTION {format.chapter.pages}
{ chapter empty$
    { pages empty$
        { ""
          "page numbers missing in " cite$ * warning$
        }
        'format.pages
      if$
    }
    { type empty$
        { "Chapter" } % gnp - changed to mixed case
        { type "t" change.case$ }
      if$
      chapter tie.or.space.connect
      pages empty$
        {"page numbers missing in " cite$ * warning$} % gnp - added check
        { ", " * format.pages * }
      if$
    }
  if$
}

FUNCTION {format.in.ed.booktitle}
{ booktitle empty$
  { "" }
  {  "\inword{} " format.emphasize.booktitle * 
    venue empty$
       { }
       { " (" venue ")"  * * *
       }
    if$
    format.bvolume 
    editor empty$
      { }
      { ", \editedbyword{} " * format.editors.fml * }
    if$
  }
  if$
}

FUNCTION {format.thesis.type}
{ type empty$
    'skip$
    { pop$
      type "t" change.case$
    }
  if$
}

FUNCTION {format.tr.number}
{ type empty$
    { "Technical Report" }
    'type
  if$
  number empty$
    { "t" change.case$ }
    { number tie.or.space.connect }
  if$
}

FUNCTION {format.article.crossref}
{ "See"
  "\citeN{" * crossref * "}" *
}

FUNCTION {format.crossref.editor}
{ editor #1 "{vv~}{ll}" format.name$
  editor num.names$ duplicate$
  #2 >
    { pop$ " et~al." * }
    { #2 <
    'skip$
    { editor #2 "{ff }{vv }{ll}{ jj}" format.name$ "others" =
        { " et~al." * }
        { " \andword{} " * editor #2 "{vv~}{ll}" format.name$ * }
      if$
    }
      if$
    }
  if$
}

FUNCTION {format.book.crossref}
{ volume empty$
    { "empty volume in " cite$ * "'s crossref of " * crossref * warning$
      "In "
    }
    { "Volume" volume tie.or.space.connect % gnp - changed to mixed case
      " of " *
    }
  if$
  editor empty$
  editor field.or.null author field.or.null =
  or
    { key empty$
    { series empty$
        { "need editor, key, or series for " cite$ * " to crossref " *
          crossref * warning$
          "" *
        }
        { "{\em " * series * "\/}" * }
      if$
    }
    { key * }
      if$
    }
    { format.crossref.editor * }
  if$
  " \citeN{" * crossref * "}" *
}

FUNCTION {format.incoll.inproc.crossref}
{ "See"
  " \citeN{" * crossref * "}" *
}

% format.lab.names:
% determines label for the abbreviated author information.
% 1st argument: string (author, editor, etc.)
% 2nd argument: #2 if von should be included, #1 if not
%
% There are 4 cases.   (n=3 in the example)
% a) one author             Foo
% b) one to n               Foo, Bar and Baz
% c) use of "and others"    Foo, Bar et al.
% d) more than n            Foo et al.
%
FUNCTION {format.lab.names}
{ 's :=
  #2 = {"{vv~}{ll}"} {"{ll}"} if$ 'v := 
  s num.names$ 'numnames :=
% SL: >2 authors triggers "et al".
  numnames #2 >    
    { s #1  v format.name$ " et~al." * }
    {
      numnames #1 - 'namesleft :=
      #2 'nameptr :=
      s #1 v format.name$
	{ namesleft #0 > }
	{ nameptr numnames =
	    { 
                numnames #2 >
% Goddam serial comma. Not used in other civilized languages.
                  { "\serialcomma" * }
                  'skip$
                if$
                s nameptr "{ff }{vv }{ll}{ jj}" format.name$ "others" =
		{ " et~al." * }
		{ " \andword{} " * s nameptr "{vv~}{ll}" format.name$ * }
	      if$
	    }
	    { ", " * s nameptr "{vv~}{ll}" format.name$ * }
	  if$
	  nameptr #1 + 'nameptr :=
	  namesleft #1 - 'namesleft :=
	}
      while$
    }
  if$
}

FUNCTION {author.key.label}
{ 
     author empty$
          { "no key, author in " cite$ * warning$
            pop$  % pop the novon parameter
            cite$ #1 #3 substring$ }
      {  author format.lab.names  }
      if$
}

FUNCTION {author.key.organization.label}
{ 
  author empty$
    { organization empty$
	    { "no key, author or organization in " cite$ * warning$
              pop$  % pop the novon parameter
              cite$ #1 #3 substring$ }
        { organization }
      if$
    }
    { author format.lab.names }
  if$
}

FUNCTION {editor.key.organization.label}
{ 
  editor empty$
    { organization empty$
	    { "no key, editor or organization in " cite$ * warning$
              pop$  % pop the novon parameter
              cite$ #1 #3 substring$ }
        { organization }
      if$
    }
    { editor format.lab.names }
  if$
}

FUNCTION {author.editor.key.label}
{ 
  author empty$
    { editor empty$
               { "no key, author, or editor in " cite$ * warning$
            pop$  % pop the novon parameter
                 cite$ #1 #3 substring$ }
          { editor format.lab.names }
      if$
    }
    { author format.lab.names }
  if$
}

% In make.label, the top element on the stack indicates whether 
% von should appear or not.  (#1 = appears, #2 = does not appear)
% This argument gets passed to the functions that actually do the
% work, or is popped (if key is given, in which case there is nothing to do)
%
FUNCTION {make.label}
{ key empty$ {
  type$ "book" =
  type$ "inbook" =
  or
    'author.editor.key.label
    { type$ "proceedings" =
	'editor.key.organization.label
	{ type$ "manual" =
	    'author.key.organization.label
	    'author.key.label
	  if$
	}
      if$
    }
  if$
  } {pop$ key} if$
"}{" *
% SL: don't take substring, don't purify
  year field.or.hook 
  'label.year :=
}

FUNCTION {vonfull.label} {#2 make.label}
FUNCTION {vonless.label} {#1 make.label}

FUNCTION {output.bibitem}
{ newline$

  "\bibitem[\protect\cay{" write$
  vonfull.label write$
  sort.year write$
  "}]{" write$

  cite$ write$
  "}" write$
  newline$
  ""
  before.all 'output.state :=
}

FUNCTION {article}
{ output.bibitem
  format.authors
  "author" output.check
  author format.key output          % added
  new.block
  format.title
  "title" output.check
  new.block
  crossref missing$
    { format.jour.vol output
    }
    { format.article.crossref output.nonnull
      format.pages output
    }
  if$
  fin.entry
}

FUNCTION {book}
{ output.bibitem
  author empty$
    { format.editors
	  "author and editor" output.check }
    { format.authors
	  output.nonnull }
  if$
  new.block
  format.btitle
  "title" output.check
%SL: allow editor even if author is present
  editor empty$
    { }
    { "\editedbyword{} " format.editors.fml *  output.nonnull }
  if$
  crossref missing$
    {
      new.block
      format.number.series output
%      new.sentence
%SL: switch address and publisher
      publisher output
      address output
%SL: move year here
  output.yearnopar.check       % added
    }
    { new.block
      format.book.crossref output.nonnull
    }
  if$
  fin.entry
}

FUNCTION {booklet}
{ output.bibitem
  format.authors output
  author format.key output          % added
  new.block
  format.title
  "title" output.check
  new.block
  howpublished output
% SL: move year here
  output.yearnopar.check                 % added
  address output
  fin.entry
}

FUNCTION {inbook}
{ output.bibitem
  author empty$
    { format.editors
      "author and editor" output.check
    }
    { format.authors output.nonnull
      crossref missing$
    { "author and editor" editor either.or.check }
    'skip$
      if$
    }
  if$
  new.block
  format.btitle
  "title" output.check
  crossref missing$
    {
      format.chapter.pages
      "chapter and pages" output.check
      new.block
      format.number.series output
%      new.sentence
%SL: switch address and publisher
      publisher output
      address output
% SL: year after publisher
  output.yearnopar.check              % added
    }
    { format.chapter.pages "chapter and pages" output.check
      new.block
      format.book.crossref output.nonnull
    }
  if$
  fin.entry
}

FUNCTION {incollection}
{ output.bibitem
  format.authors
  "author" output.check
  author format.key output       % added
  new.block
  format.title
  "title" output.check
  new.block
  crossref missing$
  { 
% SL: put pages before book title, no trailing punctuation
    format.chapter.pages " " * output 
    pages empty$ 
    {}
    {
      before.all 'output.state :=
    }
    if$
    format.in.ed.booktitle
    "booktitle" output.check
    format.number.series output
%    new.sentence
%SL: switch address and publisher
      publisher output
      address output
% SL: year after publisher
  output.yearnopar.check              % added
  }
  { format.incoll.inproc.crossref
	output.nonnull
    format.chapter.pages output
  }
  if$
  fin.entry
}

FUNCTION {conference} { incollection }
FUNCTION {inproceedings} { incollection }

FUNCTION {manual}
{ output.bibitem
  author empty$
    { editor empty$
      { organization "organization" output.check
        organization format.key output }  % if all else fails, use key
      { format.editors "author and editor" output.check }
      if$
    }
    { format.authors output.nonnull }
    if$
  new.block
  format.btitle
  "title" output.check
  organization address new.block.checkb
% Reversed the order of "address" and "organization", added the ":".
  address output
  organization "organization" output.check.colon
% SL: move year here
  output.yearnopar.check                 % added
%  address output
%  ":" output
%  organization output
  fin.entry
}

FUNCTION {mastersthesis}
{ output.bibitem
  format.authors
  "author" output.check
  author format.key output          % added
  new.block
  format.title
  "title" output.check
  new.block
  "Master's thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
% SL: move year here
  output.yearnopar.check                 % added
  fin.entry
}

FUNCTION {misc}
{ output.bibitem
  format.authors output
  author format.key output            % added
  title howpublished new.block.checkb
  format.title output
  new.block
  howpublished output
% SL: move year here
  output.yearnopar.check                   % added
  fin.entry
}

FUNCTION {phdthesis}
{ output.bibitem
  format.authors
  "author" output.check
  author format.key output            % added
  new.block
  format.btitle
  "title" output.check
  new.block
  "Ph.D. thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
% SL: move year here
  output.yearnopar.check                   % added
  fin.entry
}

FUNCTION {proceedings}
{ output.bibitem
  editor empty$
    { organization output
      organization format.key output }  % gnp - changed from author format.key
    { format.editors output.nonnull }
  if$
% author format.key output             % gnp - removed (should be either
%                                        editor or organization
  new.block
  format.btitle
  "title" output.check
  format.number.series output
%  new.sentence
%SL: switch address and publisher
      publisher output
  address output
% SL: move year here
  output.yearnopar.check                    % added (newapa)
  fin.entry
}

FUNCTION {techreport}
{ output.bibitem
  format.authors
  "author" output.check
  author format.key output             % added
  new.block
  format.title
  "title" output.check
  new.block
  format.tr.number output.nonnull
  institution
  "institution" output.check
  address output
% SL: move year here
  output.yearnopar.check                    % added
  fin.entry
}

FUNCTION {unpublished}
{ output.bibitem
  format.authors
  "author" output.check
  author format.key output              % added
  new.block
  format.title
  "title" output.check
% SL: move year here
  output.yearnopar.check                      % added
  fin.entry
}

FUNCTION {default.type} { misc }

MACRO {jan} {"\monthword{1}"}

MACRO {feb} {"\monthword{2}"}

MACRO {mar} {"\monthword{3}"}

MACRO {apr} {"\monthword{4}"}

MACRO {may} {"\monthword{5}"}

MACRO {jun} {"\monthword{6}"}

MACRO {jul} {"\monthword{7}"}

MACRO {aug} {"\monthword{8}"}

MACRO {sep} {"\monthword{9}"}

MACRO {oct} {"\monthword{10}"}

MACRO {nov} {"\monthword{11}"}

MACRO {dec} {"\monthword{12}"}

READ

FUNCTION {sortify}
{ purify$
  "l" change.case$
}

INTEGERS { len }

FUNCTION {chop.word}
{ 's :=
  'len :=
  s #1 len substring$ =
    { s len #1 + global.max$ substring$ }
    's
  if$
}



FUNCTION {sort.format.names}
{ 's :=
  #1 'nameptr :=
  ""
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
          { "   " * }
         'skip$
      if$
% SL: don't use von in sorting
%      s nameptr "{vv{ } }{ll{ }}{  f{ }}{  jj{ }}" format.name$ 't :=
      s nameptr "{ll{ }}{  f{ }}{  jj{ }}{vv{ } }" format.name$ 't :=
      nameptr numnames = t "others" = and
          { " et~al" * }
          { t sortify * }
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {sort.format.title}
{ 't :=
  "A " #2
    "An " #3
      "The " #4 t chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$
}

FUNCTION {author.sort}
{ author empty$
    { key empty$
         { "to sort, need author or key in " cite$ * warning$
           "" }
         { key sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {editor.sort}
{ editor empty$
    { key empty$
         { "to sort, need editor or key in " cite$ * warning$
           ""
         }
         { key sortify }
      if$
    }
    { editor sort.format.names }
  if$
}

FUNCTION {author.editor.sort}
{ author empty$
    { "missing author in " cite$ * warning$
      editor empty$
         { key empty$
             { "to sort, need author, editor, or key in " cite$ * warning$
               ""
             }
             { key sortify }
           if$
         }
         { editor sort.format.names }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.organization.sort}
%
% added - GNP. Stack author or organization for sorting (from alpha.bst).
% Unlike alpha.bst, we need entire names, not abbreviations
%
{ author empty$
    { organization empty$
	{ key empty$
	    { "to sort, need author, organization, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ organization sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {editor.organization.sort}
%
% added - GNP. Stack editor or organization for sorting (from alpha.bst).
% Unlike alpha.bst, we need entire names, not abbreviations
%
{ editor empty$
    { organization empty$
	{ key empty$
	    { "to sort, need editor, organization, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ organization sortify }
      if$
    }
    { editor sort.format.names }
  if$
}

FUNCTION {presort}
%
% Presort creates the bibentry's label,
% without as yet the letter that follows the year in ambiguous cases.
% This label is also the primary sort key; then comes the author name
% (or editor or organization), then title.
%
{ vonless.label sortify                 %
  " " * year field.or.hook * " " *      % first part of the sort key
  type$ "book" =
  type$ "inbook" =
  or
    'author.editor.sort
    { type$ "proceedings" =
	'editor.organization.sort
	{ type$ "manual" =
	    'author.organization.sort
	    'author.sort
	  if$
	}
      if$
    }
  if$
  #1 entry.max$ substring$        
  *
  subyear field.or.null sortify
  *
  "    "
  *
  title field.or.null
  sort.format.title
  *
  #1 entry.max$ substring$
  duplicate$
  'sort.key$ :=
  'sort.label :=
}

ITERATE {presort}

SORT             % by label, year, author/editor, title

STRINGS { cur.label last.label next.extra }

INTEGERS { last.extra.num }

FUNCTION {initialize.extra.label.stuff}
{ #0 int.to.chr$ 'last.label :=
  "" 'next.extra :=
  #0 'last.extra.num :=
}

FUNCTION {forward.pass}
%
% Pass through all entries, comparing current entry to last one.
% Need to concatenate year to the stack (done by make.label) to determine
% if two entries are the same (see presort)
%
{
  vonless.label sortify " " *  year field.or.hook * 'cur.label :=
  last.label cur.label =     % are they equal?
     { last.extra.num #1 + 'last.extra.num :=
       last.extra.num int.to.chr$ 'extra.label :=
     }
     { "a" chr.to.int$ 'last.extra.num :=
       "" 'extra.label :=
       cur.label 
       'last.label := % assign to last.label
     }
  if$
}

FUNCTION {reverse.pass}
{ next.extra "b" =
    { "a" 'extra.label := }
     'skip$
  if$
  label.year extra.label * 'sort.year :=
  extra.label 'next.extra :=
}

EXECUTE {initialize.extra.label.stuff}

ITERATE {forward.pass}

REVERSE {reverse.pass}

FUNCTION {bib.sort.order}
{ sort.label
  'sort.key$ :=
}

ITERATE {bib.sort.order}

SORT             % by sort.label, year, title --- giving final bib. order.

FUNCTION {begin.bib}

{ preamble$ empty$
    'skip$
    { preamble$ write$ newline$ }
  if$
  "\begin{thebibliography}{}" write$ newline$
}


EXECUTE {begin.bib}

EXECUTE {init.state.consts}

ITERATE {call.type$}

FUNCTION {end.bib}
{ newline$
  "\end{thebibliography}" write$ newline$
}

EXECUTE {end.bib}

