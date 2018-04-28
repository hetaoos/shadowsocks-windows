using Shadowsocks.Encryption;
using Shadowsocks.Encryption.AEAD;
using Shadowsocks.Encryption.Exception;
using Shadowsocks.Model;
using Shadowsocks.Proxy;
using Shadowsocks.Util.Sockets;
using System;
using System.Diagnostics;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Threading;

namespace Shadowsocks.Controller
{
    internal class SpeedTester
    {
        private class AsyncSession
        {
            public IProxy Remote { get; }

            public AsyncSession(IProxy remote)
            {
                Remote = remote;
            }
        }

        private readonly int _serverTimeout;
        private readonly int _proxyTimeout;

        // each recv size.
        public const int RecvSize = 2048;

        // max chunk size
        public const uint MaxChunkSize = AEADEncryptor.CHUNK_LEN_MASK + AEADEncryptor.CHUNK_LEN_BYTES + 16 * 2;

        // In general, the ciphertext length, we should take overhead into account
        public const int BufferSize = RecvSize + (int)MaxChunkSize + 32 /* max salt len */;

        private ShadowsocksController _controller;
        private Configuration _config;

        private IEncryptor _encryptor;
        private Server _server;

        private AsyncSession _currentRemoteSession;

        private bool _proxyConnected;
        private bool _destConnected;

        private int _addrBufLength = -1;

        private int _totalRead = 0;
        private int _totalWrite = 0;

        // remote -> local proxy (ciphertext, before decrypt)
        private byte[] _remoteRecvBuffer = new byte[BufferSize];

        // client -> local proxy (plaintext, before encrypt)
        private byte[] _connetionRecvBuffer = new byte[BufferSize];

        // local proxy -> remote (plaintext, after decrypt)
        private byte[] _remoteSendBuffer = new byte[BufferSize];

        // local proxy -> client (ciphertext, before decrypt)
        private byte[] _connetionSendBuffer = new byte[BufferSize];

        private bool _remoteShutdown = false;
        private bool _closed = false;

        // instance-based lock without static
        private readonly object _encryptionLock = new object();

        private readonly object _decryptionLock = new object();
        private readonly object _closeConnLock = new object();

        private DateTime _startConnectTime;
        private DateTime _startReceivingTime;
        private DateTime _startSendingTime;

        private EndPoint _destEndPoint = null;
        private ManualResetEventSlim manualResetEvent;
        private bool _received = false;

        public SpeedTester(ShadowsocksController controller, Configuration config)
        {
            _controller = controller;
            _config = config;
            _proxyTimeout = config.proxy.proxyTimeout * 1000;
            _serverTimeout = config.GetCurrentServer().timeout * 1000;
        }

        private byte[] data;

        private void CreateRemote(Server server)
        {
            _server = server;
            var ds = "03 0E 77 77 77 2E 67 6F 6F 67 6C 65 2E 63 6F 6D 01 BB 16 03 01 02 00 01 00 01 FC 03 03 41 D3 58 FA F8 62 CA AD E1 63 08 F5 42 77 8A 5B E4 83 3E 68 DC 9D 2F 3E 79 03 7A DD B9 37 FA F6 20 1F DF 53 B8 3B 2C 10 87 3B 14 24 96 29 59 8B 56 26 8B F5 10 C7 F0 3C 69 69 D9 3E C1 BB 44 DB 7F 00 22 4A 4A 13 01 13 02 13 03 C0 2B C0 2F C0 2C C0 30 CC A9 CC A8 C0 13 C0 14 00 9C 00 9D 00 2F 00 35 00 0A 01 00 01 91 5A 5A 00 00 FF 01 00 01 00 00 00 00 13 00 11 00 00 0E 77 77 77 2E 67 6F 6F 67 6C 65 2E 63 6F 6D 00 17 00 00 00 23 00 00 00 0D 00 14 00 12 04 03 08 04 04 01 05 03 08 05 05 01 08 06 06 01 02 01 00 05 00 05 01 00 00 00 00 00 12 00 00 00 10 00 0E 00 0C 02 68 32 08 68 74 74 70 2F 31 2E 31 75 50 00 00 00 0B 00 02 01 00 00 33 00 2B 00 29 DA DA 00 01 00 00 1D 00 20 6F 95 7B D4 11 D8 C7 70 42 26 38 35 BB 3E AE FA 72 49 B1 D0 DF 3F 98 C2 A2 BB CD 46 26 50 BD 3F 00 2D 00 02 01 01 00 2B 00 0B 0A FA FA 7F 17 03 03 03 02 03 01 00 0A 00 0A 00 08 DA DA 00 1D 00 17 00 18 FA FA 00 01 00 00 15 00 CD 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00";
            data = ds.Split(new string[] { " " }, StringSplitOptions.RemoveEmptyEntries).Select(o => (byte)int.Parse(o, System.Globalization.NumberStyles.HexNumber)).ToArray();
            _addrBufLength = 18;
            _encryptor = EncryptorFactory.GetEncryptor(_server.method, _server.password);
            /* prepare address buffer length for AEAD */
            Logging.Debug($"_addrBufLength={_addrBufLength}");
            _encryptor.AddrBufLength = _addrBufLength;
        }

        private void CheckClose()
        {
            if (_remoteShutdown)
                Close();
        }

        public void Close()
        {
            manualResetEvent?.Set();
            lock (_closeConnLock)
            {
                if (_closed) return;
                _closed = true;
            }

            if (_currentRemoteSession != null)
            {
                try
                {
                    var remote = _currentRemoteSession.Remote;
                    remote.Shutdown(SocketShutdown.Both);
                    remote.Close();
                }
                catch (Exception e)
                {
                    Logging.LogUsefulException(e);
                }
            }

            lock (_encryptionLock)
            {
                lock (_decryptionLock)
                {
                    _encryptor?.Dispose();
                }
            }
        }

        public void Run(Action onFinish)
        {
            Action ac = () =>
            {
                var cfgs = _config.configs.ToList();
                foreach (var sv in cfgs)
                {
                    var i1 = StartTest(sv);
                    if (i1 == 0)
                    {
                        sv.speed = 0;
                        continue;
                    }
                    var i2 = StartTest(sv);
                    if (i2 == 0)
                        sv.speed = i1;
                    else
                        sv.speed = Math.Min(i1, i2);
                }
                int i = 1;
                foreach (var sv in cfgs.Where(o => o.speed > 0).OrderBy(o => o.speed))
                {
                    sv.speed_index = i++;
                }
                foreach (var sv in cfgs.Where(o => o.speed == 0))
                    sv.speed_index = 0;

            };
            ac.BeginInvoke((o) => onFinish?.Invoke(), null);
        }

        /// <summary>
        /// 测试速度
        /// </summary>
        /// <param name="server">服务器</param>
        /// <param name="millisecondsTimeout">超时时间</param>
        /// <returns></returns>
        public int StartTest(Server server, int millisecondsTimeout = 1000)
        {
            _closed = false;
            try
            {
                CreateRemote(server);
                // Setting up proxy
                IProxy remote;
                EndPoint proxyEP = null;
                EndPoint serverEP = SocketUtil.GetEndPoint(_server.server, _server.server_port);
                EndPoint pluginEP = _controller.GetPluginLocalEndPointIfConfigured(_server);

                if (pluginEP != null)
                {
                    serverEP = pluginEP;
                    remote = new DirectConnect();
                }
                else if (_config.proxy.useProxy)
                {
                    switch (_config.proxy.proxyType)
                    {
                        case ProxyConfig.PROXY_SOCKS5:
                            remote = new Socks5Proxy();
                            break;

                        case ProxyConfig.PROXY_HTTP:
                            remote = new HttpProxy();
                            break;

                        default:
                            throw new NotSupportedException("Unknown forward proxy.");
                    }
                    proxyEP = SocketUtil.GetEndPoint(_config.proxy.proxyServer, _config.proxy.proxyPort);
                }
                else
                {
                    remote = new DirectConnect();
                }

                var session = new AsyncSession(remote);
                lock (_closeConnLock)
                {
                    if (_closed)
                    {
                        remote.Close();
                        return 0;
                    }

                    _currentRemoteSession = session;
                }

                _destEndPoint = serverEP;

                _proxyConnected = false;
                _received = false;
                manualResetEvent = new ManualResetEventSlim(false);
                Stopwatch sw = new Stopwatch();
                sw.Start();
                remote.BeginConnectProxy(proxyEP, ProxyConnectCallback,
                    new AsyncSession(remote));
                manualResetEvent.Wait(millisecondsTimeout);
                sw.Stop();
                Close();
                if (_received)
                    return (int)sw.ElapsedMilliseconds;
                return 0;
            }
            catch (Exception e)
            {
                Close();
            }
            finally
            {
                manualResetEvent?.Dispose();
                manualResetEvent = null;
            }
            return 0;
        }

        private void ProxyConnectCallback(IAsyncResult ar)
        {
            if (_closed)
            {
                manualResetEvent?.Set();
                return;
            }
            try
            {
                var session = (AsyncSession)ar.AsyncState;

                var remote = session.Remote;

                // Complete the connection.
                remote.EndConnectProxy(ar);

                _proxyConnected = true;

                if (_config.isVerboseLogging)
                {
                    if (!(remote is DirectConnect))
                    {
                        Logging.Info($"Socket connected to proxy {remote.ProxyEndPoint}");
                    }
                }

                _startConnectTime = DateTime.Now;

                _destConnected = false;
                remote.BeginConnectDest(_destEndPoint, ConnectCallback,
                    new AsyncSession(session.Remote));
            }
            catch (ArgumentException)
            {
            }
            catch (Exception e)
            {
                Close();
            }
        }

        private void ConnectCallback(IAsyncResult ar)
        {
            if (_closed)
            {
                manualResetEvent?.Set();
                return;
            }
            try
            {
                var session = (AsyncSession)ar.AsyncState;

                var remote = session.Remote;
                // Complete the connection.
                remote.EndConnectDest(ar);
                _destConnected = true;
                StartPipe(session);
            }
            catch (ArgumentException)
            {
            }
            catch (Exception e)
            {
                Close();
            }
        }

        private void StartPipe(AsyncSession session)
        {
            if (_closed)
            {
                manualResetEvent?.Set();
                return;
            }
            try
            {
                _startReceivingTime = DateTime.Now;
                session.Remote.BeginReceive(_remoteRecvBuffer, 0, RecvSize, SocketFlags.None,
                    PipeRemoteReceiveCallback, session);

                SendToServer(session);
            }
            catch (Exception e)
            {
                Close();
            }
        }

        private void PipeRemoteReceiveCallback(IAsyncResult ar)
        {
            if (_closed)
            {
                manualResetEvent?.Set();
                return;
            }
            try
            {
                var session = (AsyncSession)ar.AsyncState;
                int bytesRead = session.Remote.EndReceive(ar);
                _totalRead += bytesRead;
                if (bytesRead > 0)
                {
                    int bytesToSend = -1;
                    lock (_decryptionLock)
                    {
                        try
                        {
                            _encryptor.Decrypt(_remoteRecvBuffer, bytesRead, _remoteSendBuffer, out bytesToSend);
                        }
                        catch (CryptoErrorException)
                        {
                            Close();
                            return;
                        }
                    }
                    _received = bytesToSend > 0;
                    manualResetEvent?.Set();
                }
                else
                {
                    CheckClose();
                }
            }
            catch (Exception e)
            {
                Close();
            }
        }

        private void SendToServer(AsyncSession session)
        {
            var length = data.Length;
            _totalWrite += length;
            int bytesToSend;
            Array.Copy(data, _connetionRecvBuffer, data.Length);
            lock (_encryptionLock)
            {
                try
                {
                    _encryptor.Encrypt(_connetionRecvBuffer, length, _connetionSendBuffer, out bytesToSend);
                }
                catch (CryptoErrorException)
                {
                    Close();
                    return;
                }
            }
            _startSendingTime = DateTime.Now;
            session.Remote.BeginSend(_connetionSendBuffer, 0, bytesToSend, SocketFlags.None,
                PipeRemoteSendCallback, new object[] { session, bytesToSend });
        }

        private void PipeRemoteSendCallback(IAsyncResult ar)
        {
            if (_closed)
            {
                manualResetEvent?.Set();
                return;
            }
            try
            {
                var container = (object[])ar.AsyncState;
                var session = (AsyncSession)container[0];
                var bytesShouldSend = (int)container[1];
                int bytesSent = session.Remote.EndSend(ar);
                int bytesRemaining = bytesShouldSend - bytesSent;
                if (bytesRemaining > 0)
                {
                    Buffer.BlockCopy(_connetionSendBuffer, bytesSent, _connetionSendBuffer, 0, bytesRemaining);
                    session.Remote.BeginSend(_connetionSendBuffer, 0, bytesRemaining, SocketFlags.None,
                        PipeRemoteSendCallback, new object[] { session, bytesRemaining });
                    return;
                }
            }
            catch (Exception e)
            {
                Close();
            }
        }
    }
}