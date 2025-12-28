import { Popup } from '../Navigation';
import { FC, FormEvent, useRef, useState } from 'react';

const LoadUrlPopup: FC<{
  open: boolean;
  handleClose: () => void;
  loadFromUrl: (url: string) => void;
}> = ({ open, handleClose, loadFromUrl }) => {
  const [error, setError] = useState('');
  const urlRef = useRef<HTMLInputElement>(null);

  const handleLoad = (ev: FormEvent) => {
    ev.preventDefault();
    let url = urlRef.current?.value;
    if (!url) {
      setError(`Please specify a URL.`);
      return;
    }
    if (!url.startsWith('http://') && !url.startsWith('https://')) {
      url = 'https://' + url;
    }
    loadFromUrl(url);
    handleClose();
  };

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Load from URL</h2>
      {error ? <p className="form-error">{error}</p> : null}
      <form onSubmit={handleLoad}>
        <input name="import URL" autoFocus type="text" placeholder="Paste URL here" ref={urlRef} />
        <input type="submit" value="Load" />
      </form>
    </Popup>
  );
};

export default LoadUrlPopup;
