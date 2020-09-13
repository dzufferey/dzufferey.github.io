"use strict";

function formatTitle(publication) {
    var a = document.createElement('a');
    if (publication['link-paper'] !== undefined) {
        a.setAttribute('href', publication['link-paper']);
    } else {
        a.setAttribute('href', '#');
    }
    a.innerHTML = publication['title'];
    var h4 = document.createElement('h4');
    h4.setAttribute('class', "modal-title");
    h4.appendChild(a);
    return h4;
}

function formatAuthors(publication) {
    var text = "";
    for (var i = 0; i < publication.author.length; i++) {
       if (i > 0 && publication.author.length > 2) {
           text += ", ";
       }
       if (i === publication.author.length - 1 && publication.author.length > 1) {
           if (i === 1) {
               text += " and ";
           } else {
               text += "and ";
           }
       }
       var n = publication.author[i];
       text += n.given + " " + n.family;
    }
    var a = document.createElement('div');
    a.setAttribute('class', "pub-authors");
    a.innerHTML = text;
    return a;
}

function formatVenue(publication) {
    var a = document.createElement('div');
    a.setAttribute('class', "pub-venue");
    if (publication['container-title'] !== undefined) {
        a.innerHTML = publication['container-title'] + ", " + publication.issued['date-parts'][0];
    } else {
        a.innerHTML = publication['publisher'] + ", " + publication.issued['date-parts'][0];
    }
    return a;
}

function mkBtnLink(name, lnk) {
    var a = document.createElement('a');
    a.setAttribute('href', lnk);
    a.setAttribute('class', "btn btn-primary");
    var ext = lnk.split(".");
    a.innerHTML = name + " (" + ext[ext.length-1] + ")";
    return a;
}

function formatLinks(publication) {
    var l = document.createElement('div');
    l.setAttribute('class', "pub-link btn-group btn-group-justified");
    if (publication['link-paper'] !== undefined) {
        l.appendChild(mkBtnLink("Paper", publication['link-paper']));
    }
    if (publication['link-slides'] !== undefined) {
        l.appendChild(mkBtnLink("Slides", publication['link-slides']));
    }
    if (publication['link-poster'] !== undefined) {
        l.appendChild(mkBtnLink("Poster", publication['link-poster']));
    }
    return l;
}

function formatAbstract(publication) {
    var l = document.createElement('div');
    l.setAttribute('class', "pub-abstract");
    if (publication['abstract'] !== undefined) {
        var paragraphs = publication['abstract'].split("\n");
        for (var i = 0; i < paragraphs.length; i++) {
            var p = document.createElement('p');
            p.innerHTML = paragraphs[i];
            l.appendChild(p);
        }
    }
    return l;
}

function createModal(id, publication) {
    var mod = document.createElement('div');
    mod.setAttribute('id', id);
    mod.setAttribute('class', "modal fade");
    mod.setAttribute('role', "dialog");
    var dia = document.createElement('div');
    dia.setAttribute('class', "modal-dialog modal-lg");
    var cnt = document.createElement('div');
    cnt.setAttribute('class', "modal-content");

    var header = document.createElement('div');
    header.setAttribute('class', "modal-header");
    var bt1 = document.createElement('button');
    bt1.setAttribute('type', "button");
    bt1.setAttribute('class', "close");
    bt1.setAttribute('data-dismiss', "modal");
    bt1.innerHTML = "&times;";
    header.appendChild(bt1);
    header.appendChild(formatTitle(publication));

    var body = document.createElement('div');
    body.setAttribute('class', "modal-body");
    body.appendChild(formatAuthors(publication));
    body.appendChild(formatVenue(publication));
    body.appendChild(formatLinks(publication));
    if (publication['abstract'] !== undefined) {
        var divider = document.createElement('hr');
        divider.setAttribute('class', "divider");
        body.appendChild(divider);
        body.appendChild(formatAbstract(publication));
    }

    var footer = document.createElement('div');
    footer.setAttribute('class', "modal-footer");
    var bt2 = document.createElement('button');
    bt2.setAttribute('type', "button");
    bt2.setAttribute('class', "btn btn-default");
    bt2.setAttribute('data-dismiss', "modal");
    bt2.innerHTML = "Close";
    footer.appendChild(bt2);

    cnt.appendChild(header);
    cnt.appendChild(body);
    cnt.appendChild(footer);

    dia.appendChild(cnt);
    mod.appendChild(dia);
    return mod;
}

var counter = 0;

function makeListAndModal(data, targetID) {
    var items = [];
    var modals = [];

    for (var i=0; i < data.length; i++) {
        var pub = data[i];
        counter = counter + 1;
        var id = "pub" + counter;
        var cnt = "<h4 class='list-group-item-heading'>"+ pub['title'] +"</h4><div class='list-group-item-text'>" +
                  formatAuthors(pub).outerHTML +
                  formatVenue(pub).outerHTML +
                  "</div>";
        items.push("<a class='list-group-item clickable' data-toggle='modal' data-target='#"+id+"'>" + cnt + "</a>" );
        modals.push(createModal(id, pub));
    }

    $( "<div/>", {
       "class": "list-group",
       html: items.join( "" )
    }).appendTo( targetID );

    var woSharp = targetID.substring(1, targetID.length);
    var d = document.getElementById(woSharp);
    for (var i=0; i < modals.length; i++) {
        d.appendChild( modals[i] );
    }
}

function loadPub() {
    var source = "publications.json";
    var recentID = "#pub-recent";
    var allID = "#pub-all";
    var kinds = {
        "journal": "Journal Paper",
        "conf": "Conference Papers",
        "thesis": "Thesis",
        "workshop": "Workshop Papers",
        "techrep": "Technical Reports"
    };
    $.getJSON( source, function( data ) {
        //clean-up
        $(recentID).children().remove();
        $(recentID).append("<p></p>");
        $(allID).children().remove();
        $(allID).append("<p></p>");
        //recent
        var recentPub = $.grep( data, function (pub) { return pub.tag === "recent" });
        makeListAndModal(recentPub, recentID);
        //all
        $.each( kinds, function( key, name) {
            var relevant = $.grep( data, function (pub) { return pub.keyword === key });
            $(allID).append("<h3>"+name+"</h3>");
            makeListAndModal(relevant, allID);
        });
    });
}

loadPub();
