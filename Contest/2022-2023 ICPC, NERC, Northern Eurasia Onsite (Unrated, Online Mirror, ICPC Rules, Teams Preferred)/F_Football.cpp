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
#define rep(i, a, b) for (ll i = (a); i < (b); ++i)
#define rev(i, a, b) for (ll i = (a); i >= (b); --i)
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
 void solve(ll &n, ll &a, ll &b)
{
    ll cnt = 0, m = a, k = b;
    vector<pair<ll, ll>> v(n);
    for (ll i = 0; i < n; i++)
    {
        if (i % 2 == 0 && a > 0)
        {
            v[i].first++;
            a--;
        }
        else
            v[i].first = 0;
        if (i % 2 == 1 && b > 0)
        {
            v[i].second++;
            b--;
        }
        else
            v[i].second = 0;
    }
    for (ll i = n - 1; i >= 0; i--)
    {
        if (v[i].second == 0 && v[i].first != 1 && a > 0)
        {
            v[i].first++;
            a--;
        }
        if (v[i].first == 0 && v[i].second != 1 && b > 0)
        {
            v[i].second++;
            b--;
        }
        if (a == 0 && b == 0)
            break;
    }
    v[0].first += a;
    v[1].second += b;
    int ans = (n <= m + k) ? 0 : (n - m - k);
    cout << ans << endl;
    for (ll i = 0; i < n; i++)
    {
        cout << v[i].first << ":" << v[i].second << endl;
    }
}
 int main()
{
    fastIO;
    ll n, a, b, cnt = 0;
    cin >> n >> a >> b;
    if (n == 1)
    {
        if (a == b)
            cout << 1 << endl;
        else
            cout << 0 << endl;
        cout << a << ":" << b << endl;
    }
    else
    {
        solve(n, a, b);
    }
}