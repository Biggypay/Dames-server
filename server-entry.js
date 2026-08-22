'use strict';

const path = require('path');
const expressPath = require.resolve('express');
const originalExpress = require(expressPath);

function wrappedExpress(...args) {
  const app = originalExpress(...args);
  app.get('/dames-local', (req, res) => {
    res.setHeader('Cache-Control', 'no-store');
    res.sendFile(path.join(__dirname, 'public', 'dames-local.html'));
  });
  return app;
}

Object.assign(wrappedExpress, originalExpress);
require.cache[expressPath].exports = wrappedExpress;
require('./server.js');
