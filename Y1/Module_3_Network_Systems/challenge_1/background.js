
function onrequest(req) {
  // This function will be called everytime the browser is about to send out an http or https request.
  // The req variable contains all information about the request.
  // If we return {}, the request will be performed, without any further changes
  // If we return {cancel:true}, the request will be cancelled.
  // If we return {requestHeaders:req.requestHeaders}, any modifications made to the requestHeaders (see below) are sent.

  let blocked_keywords = ['analytics', 'ads', 'amazon', 'metrics', 'ping', 'privacy', 'logs', 'optimizely']

  // log what file we're going to fetch:
  console.log("Loading: " + req.method +" "+ req.url + " "+ req.type);

  // let's do something special if an image is loaded:
  if (req.type=="image") {
     console.log("Ooh, it's a picture!");
  }


  // This will modify the User-Agent Header
  for (let header of req.requestHeaders) {
    if (header.name == 'User-Agent') {
      header.value = 'None of your business';
      break;
    }
  }
  // The IP cannot be hidden as the server needs the ip address to return the requeste page

  // Block tracking urls
  for (let keyword of blocked_keywords) {
    if (req.url.includes(keyword)) {
      return {cancel:true};
    }
  }

  console.log(req)

  // req also contains an array called requestHeaders containing the name and value of each header.
  // You can access the name and value of the i'th header as req.requestHeaders[i].name and req.requestHeaders[i].value,
  // with i from 0 up to (but not including!) req.requestHeaders.length

  return {requestHeaders:req.requestHeaders};
}


// no need to change the following! This just makes sure that the above function is called whenever the browser wants to fetch a file
browser.webRequest.onBeforeSendHeaders.addListener(
  onrequest,
  {urls: ["<all_urls>"]},
  ["blocking", "requestHeaders"]
);

