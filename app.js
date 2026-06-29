(function(){
function $(id){return document.getElementById(id);}
var VL=window.VL||{};
function esc(s){return String(s==null?"":s).replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;");}
function fmtSize(n){if(n<1024)return n+" B";if(n<1048576)return (n/1024).toFixed(1)+" KB";return (n/1048576).toFixed(2)+" MB";}
function gcd(a,b){return b?gcd(b,a%b):a;}
function aspect(w,h){if(!w||!h)return "-";var g=gcd(w,h);return (w/g)+":"+(h/g);}

// ---- format by signature ----
function ascii(b,i,n){var s="";for(var k=0;k<n;k++)s+=String.fromCharCode(b[i+k]);return s;}
function detect(b){
  if(b.length<4)return {f:"?",mime:""};
  if(b[0]==0xFF&&b[1]==0xD8&&b[2]==0xFF)return {f:"JPEG",mime:"image/jpeg",ext:["jpg","jpeg","jpe"]};
  if(b[0]==0x89&&b[1]==0x50&&b[2]==0x4E&&b[3]==0x47)return {f:"PNG",mime:"image/png",ext:["png"]};
  if(b[0]==0x47&&b[1]==0x49&&b[2]==0x46&&b[3]==0x38)return {f:"GIF",mime:"image/gif",ext:["gif"]};
  if(b[0]==0x42&&b[1]==0x4D)return {f:"BMP",mime:"image/bmp",ext:["bmp"]};
  if(b[0]==0x00&&b[1]==0x00&&b[2]==0x01&&b[3]==0x00)return {f:"ICO",mime:"image/x-icon",ext:["ico"]};
  if(b[0]==0x38&&b[1]==0x42&&b[2]==0x50&&b[3]==0x53)return {f:"PSD",mime:"image/vnd.adobe.photoshop",ext:["psd"]};
  if((b[0]==0x49&&b[1]==0x49&&b[2]==0x2A&&b[3]==0x00)||(b[0]==0x4D&&b[1]==0x4D&&b[2]==0x00&&b[3]==0x2A))return {f:"TIFF",mime:"image/tiff",ext:["tif","tiff"]};
  if(ascii(b,0,4)=="RIFF"&&ascii(b,8,4)=="WEBP")return {f:"WebP",mime:"image/webp",ext:["webp"]};
  if(ascii(b,4,4)=="ftyp"){var br=ascii(b,8,4).toLowerCase();
    if(br.indexOf("avif")>=0||br.indexOf("avis")>=0)return {f:"AVIF",mime:"image/avif",ext:["avif"]};
    if(br.indexOf("heic")>=0||br.indexOf("heix")>=0||br.indexOf("hevc")>=0||br.indexOf("heim")>=0||br.indexOf("heis")>=0||br.indexOf("mif1")>=0||br.indexOf("msf1")>=0||br.indexOf("heif")>=0)return {f:"HEIC",mime:"image/heic",ext:["heic","heif"]};
  }
  return {f:"?",mime:""};
}
// ---- PNG IHDR color ----
function pngInfo(dv){
  try{var bd=dv.getUint8(24),ct=dv.getUint8(25);
    var map={0:["Grayscale",false],2:["RGB",false],3:["Indexed (palette)",false],4:["Grayscale+Alpha",true],6:["RGBA",true]};
    var m=map[ct]||["?",false];return {bitdepth:bd,colortype:m[0],alpha:m[1]};
  }catch(e){return null;}
}
// ---- EXIF (JPEG APP1 / TIFF IFD) ----
function readExif(buf){
  var dv=new DataView(buf);
  if(dv.byteLength<4||dv.getUint16(0)!=0xFFD8)return null;
  var off=2;
  while(off+4<=dv.byteLength){
    var marker=dv.getUint16(off);
    if((marker&0xFF00)!=0xFF00)break;
    if(marker==0xFFE1){
      var size=dv.getUint16(off+2);
      if(off+10<=dv.byteLength&&dv.getUint32(off+4)==0x45786966&&dv.getUint16(off+8)==0x0000)
        return parseTiff(dv,off+10);
    }
    if(marker==0xFFDA||marker==0xFFD9)break;
    off+=2+dv.getUint16(off+2);
  }
  return null;
}
function parseTiff(dv,base){
  var le=dv.getUint16(base)==0x4949;
  function u16(o){return dv.getUint16(base+o,le);}
  function u32(o){return dv.getUint32(base+o,le);}
  if(u16(2)!=0x002A)return null;
  var out={};
  var WANT={0x010F:"make",0x0110:"model",0x0112:"orientation",0x0131:"software",
            0x9003:"datetime",0x9004:"datetimedigitized",0x829A:"exposure",0x829D:"fnumber",
            0x8827:"iso",0x8833:"iso",0x920A:"focal",0xA434:"lens",0xA432:"lens"};
  function val(eo){
    var type=u16(eo+2),cnt=u32(eo+4);
    var bs={1:1,2:1,3:2,4:4,5:8,7:1,9:4,10:8}[type]||1;
    var total=bs*cnt, po=(total<=4)?(eo+8):u32(eo+8);
    if(type==2){var s="";for(var i=0;i<cnt&&base+po+i<dv.byteLength;i++){var c=dv.getUint8(base+po+i);if(c==0)break;s+=String.fromCharCode(c);}return s.trim();}
    if(type==3)return u16(po);
    if(type==4)return u32(po);
    if(type==5){var n=u32(po),d=u32(po+4);return d?n/d:0;}
    if(type==10){var n2=dv.getInt32(base+po,le),d2=dv.getInt32(base+po+4,le);return d2?n2/d2:0;}
    return u16(po);
  }
  function readIFD(ifd){
    if(!ifd||base+ifd+2>dv.byteLength)return;
    var n=u16(ifd);
    for(var i=0;i<n;i++){
      var eo=ifd+2+i*12; if(base+eo+12>dv.byteLength)break;
      var tag=u16(eo);
      if(tag==0x8769){readIFD(u32(eo+8));continue;}
      if(tag==0x8825){readGPS(u32(eo+8));continue;}
      if(WANT[tag]!=null){try{var v=val(eo);if(out[WANT[tag]]==null)out[WANT[tag]]=v;}catch(e){}}
    }
  }
  function gpsCoord(ifd,tagD,tagR){
    // returns decimal degrees or null
    var n=u16(ifd),deg=null,ref=null;
    for(var i=0;i<n;i++){var eo=ifd+2+i*12,tag=u16(eo);
      if(tag==tagR){var s="";for(var k=0;k<2;k++){var c=dv.getUint8(base+eo+8+k);if(c)s+=String.fromCharCode(c);}ref=s;}
      if(tag==tagD){var po=u32(eo+8);
        function rat(o){var nn=u32(po+o),dd=u32(po+o+4);return dd?nn/dd:0;}
        deg=rat(0)+rat(8)/60+rat(16)/3600;}
    }
    if(deg==null)return null;
    if(ref=="S"||ref=="W")deg=-deg;
    return deg;
  }
  function readGPS(ifd){
    if(!ifd||base+ifd+2>dv.byteLength)return;
    var lat=gpsCoord(ifd,0x0002,0x0001),lon=gpsCoord(ifd,0x0004,0x0003);
    if(lat!=null&&lon!=null)out.gps=lat.toFixed(6)+", "+lon.toFixed(6);
  }
  readIFD(u32(4));
  return out;
}
function fmtExif(e){
  var o={};
  if(e.make)o.make=e.make;
  if(e.model)o.model=e.model;
  if(e.lens)o.lens=e.lens;
  if(e.datetime)o.datetime=e.datetime;
  if(e.exposure){var x=e.exposure;o.exposure=(x>0&&x<1)?("1/"+Math.round(1/x)+" s"):(x+" s");}
  if(e.fnumber)o.fnumber="f/"+(Math.round(e.fnumber*10)/10);
  if(e.iso)o.iso=e.iso;
  if(e.focal)o.focal=(Math.round(e.focal*10)/10)+" mm";
  if(e.orientation)o.orientation=e.orientation;
  if(e.software)o.software=e.software;
  if(e.gps)o.gps=e.gps;
  return o;
}
// ---- render ----
function row(k,v){return '<tr><td class="k">'+esc(VL[k]||k)+'</td><td class="v">'+esc(v)+'</td></tr>';}
function show(file,buf,dim,png){
  var b=new Uint8Array(buf.slice(0,32));
  var det=detect(b);
  var name=file.name||"";
  var ext=(name.split(".").pop()||"").toLowerCase();
  var mism=(det.ext&&det.ext.indexOf(ext)<0)?(" "+(VL.ext_mismatch||"")):"";
  var h='<h3>'+esc(VL.basic||"Basic info")+'</h3><table class="meta">';
  h+=row("filename",name);
  h+=row("format",det.f+mism);
  if(dim){h+=row("dimensions",dim.w+" x "+dim.h);
    h+=row("megapixels",((dim.w*dim.h)/1e6).toFixed(1));
    h+=row("aspect",aspect(dim.w,dim.h));}
  h+=row("filesize",fmtSize(file.size)+" ("+file.size+" B)");
  if(file.lastModified)h+=row("modified",new Date(file.lastModified).toLocaleString());
  if(png){h+=row("colortype",png.colortype);h+=row("bitdepth",png.bitdepth);h+=row("alpha",png.alpha?(VL.yes||"Yes"):(VL.no||"No"));}
  h+='</table>';
  var e=readExif(buf);
  if(e){var fe=fmtExif(e);var ks=Object.keys(fe);
    if(ks.length){h+='<h3>'+esc(VL.exifhead||"EXIF metadata")+'</h3><table class="meta">';
      ks.forEach(function(k){h+=row(k,fe[k]);});h+='</table>';}
    else h+='<p class="noexif">'+esc(VL.noexif||"")+'</p>';
  }else h+='<p class="noexif">'+esc(VL.noexif||"")+'</p>';
  $("out").innerHTML=h;
}
function handle(file){
  if(!file)return;
  $("out").innerHTML='<p class="muted">'+esc(VL.choosing||"Reading...")+'</p>';
  var fr=new FileReader();
  fr.onload=function(){
    var buf=fr.result;
    var dv=new DataView(buf);
    var b=new Uint8Array(buf.slice(0,32));
    var det=detect(b);
    var png=(det.f=="PNG")?pngInfo(dv):null;
    // dimensions via Image()
    var url=URL.createObjectURL(file);
    var img=new Image();
    img.onload=function(){show(file,buf,{w:img.naturalWidth,h:img.naturalHeight},png);URL.revokeObjectURL(url);};
    img.onerror=function(){show(file,buf,null,png);URL.revokeObjectURL(url);};
    img.src=url;
  };
  fr.readAsArrayBuffer(file);
}
function init(){
  var dz=$("drop"),fi=$("file");
  if(fi)fi.addEventListener("change",function(e){if(e.target.files[0])handle(e.target.files[0]);});
  if(dz){
    dz.addEventListener("click",function(){fi&&fi.click();});
    dz.addEventListener("dragover",function(e){e.preventDefault();dz.classList.add("over");});
    dz.addEventListener("dragleave",function(){dz.classList.remove("over");});
    dz.addEventListener("drop",function(e){e.preventDefault();dz.classList.remove("over");
      var f=e.dataTransfer.files&&e.dataTransfer.files[0];if(f)handle(f);});
  }
}
if(document.readyState!="loading")init();else document.addEventListener("DOMContentLoaded",init);
})();