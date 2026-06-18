#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 void solve()
{
    vector<ll> v;
    int n, m;
    cin >> n >> m;
    v.resize(n * m);
    for (int i = 0; i < n * m; i++)
        cin >> v[i];
    sort(all(v));
    ll a, b, c, d;
    a = v[n * m - 1];
    b = v[n * m - 2];
    c = v[0];
    d = v[1];
    ll mt = (n - 1) * (a - d);
    mt += ((a - c) * n * (m - 1));
    ll f = (n - 1) * (b - c);
    f += ((a - c) * (m - 1) * n);
    swap(n, m);
    ll p2 = (n - 1) * (b - c);
    p2 += ((a - c) * (m - 1) * n);
    ll nt = (n - 1) * (a - d);
    nt += ((a - c) * n * (m - 1));
    f = max(f, p2);
    p2 = max(mt, nt);
    f = max(f, p2);
    cout << f << '\n';
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}