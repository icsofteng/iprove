const express = require('express');
const app = express();
const bodyParser = require('body-parser');
const http = require('http');

// Configuration
app.use(bodyParser.urlencoded({ extended: true }));
app.use(bodyParser.json());

app.use(express.static(__dirname + '/public'));

// Start server
const port = process.env.PORT || 8080;
http.createServer(app).listen(port);
console.log('Listening on port ' + port);