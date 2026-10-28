# Bibliothèques servies par le serveur de jeux

## `three-r128.min.js` — Three.js r128

- Origine : le fichier `build/three.min.js` du paquet npm `three@0.128.0`
  (licence MIT, en-tête conservé).
- Archive vérifiée le 2026-10-28 contre l'intégrité publiée par le registre npm :
  `sha512-i0ap/E+OaSfzw7bD1TtYnPo3VEplkl70WX5fZqZnfZsE3k3aSFudqrrC9ldFZfYFkn1zwDmBcdGfiIm/hnbyZA==`.
- Empreintes du fichier (603 445 octets) :
  - SHA-256 `9274bbcec8d96168626c732b5d31c775aa8cfb7eaa0599bec0c175908a2c1ce2`
  - SHA-384 (base64) `CI3ELBVUz9XQO+97x6nwMDPosPR5XvsxW2ua7N1Xeygeh1IxtgqtCkGfQY9WWdHu`
  - SHA-512 (base64) `dLxUelApnYxpLt6K2iomGngnHO83iUvZytA3YjDUCjT0HDOHKXnVYdf3hU4JjM8uEhxf9nD1/ey98U3t2vZ0qQ==`

`server.js` (`/vendor/three-r128.min.js`) ne sert ce fichier — ou, s'il manque,
la copie d'un CDN — que si son SHA-384 est exactement celui ci-dessus. Le serveur
téléchargeait la bibliothèque à chaque démarrage sans la vérifier et la servait
depuis sa propre origine à tous les plateaux : un certificat compromis (alerte
eMudhra d'octobre 2026) ou un CDN altéré aurait suffi à injecter du code dans
chaque partie. Changer de version = remplacer le fichier ET l'empreinte
`THREE_RUNTIME_SHA384` de `server.js`.
