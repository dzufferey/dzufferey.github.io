'use strict';

var md = window.markdownit({
          linkify: true,
          highlight: function (str, lang) {
            if (lang && lang != "graphviz" && hljs.getLanguage(lang)) {
              try {
                return hljs.highlight(lang, str).value;
              } catch (__) {}
            }
            return ''; // use external default escaping
          }
        });
//var mk = require('markdown-it-katex');
//md.use(mk);

function setBody(elem) {
  document.body.innerHTML = '';
  document.body.appendChild(elem);
}

function showError(txt) {
  console.error(txt);
  var elem = document.createElement('div');
  elem.innerHTML = txt;
  setBody(elem)
}

function renderGraphviz(gv, node) {
  var viz = new Viz({ workerURL: '../lib/lite.render.js' });
  //console.log(gv);
  viz.renderSVGElement(gv)
  //viz.renderSVGElement('digraph { a -> b; }')
    .then(function(element) {
      console.log("graph rendered");
      var dv = document.createElement('div');
      dv.appendChild(element);
      node.parentNode.replaceChild(dv, node);
    })
    .catch(error => {
      // Possibly display the error
      console.error(error);
  });;
}

function loadAndDisplay(fileName) {
  //fetch the page
  var client = new XMLHttpRequest();
  client.open('GET', '/'+fileName);
  client.onreadystatechange = function() {
    if (client.readyState === 4 && client.status === 200) {
      var text = client.responseText;
      //display raw text
      var elem = document.createElement('pre');
      elem.innerHTML = text
      setBody(elem);
      //format and display
      var result = md.render(text);
      var rendered = document.createElement('div');
      rendered.classList.add("markdown-body");
      rendered.style.padding = "10%";
      rendered.innerHTML = result;
      setBody(rendered);
      console.log("rendering math");
      renderMathInElement(document.body, {
        delimiters: [
          {left: "$", right: "$", display: false},
          {left: "\\[", right: "\\]", display: true}
        ]
      });
      console.log("rendering graphs");
      var graphs = document.getElementsByClassName('language-graphviz');
      for (var i = 0, length = graphs.length; i < length; i++) {
        var pre = graphs[i].parentNode;
        var content = graphs[i].textContent;
        renderGraphviz(content, pre);
      }
    } else if (client.readyState === 4) {
      showError("Error: " + client.status);
    }
  }
  client.send();
}

//extract param
var params = new URLSearchParams(window.location.search)
if (params.has("md")) {
  var fileName = params.get("md")
  loadAndDisplay(fileName);
} else {
  showError("Error. Could not find the source file (src parameter in the URL).");
}
