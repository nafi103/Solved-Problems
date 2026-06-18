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
    ll n, ans = INT_MAX;
    cin >> n;
    vector<ll> v(n);
    set<ll> s;
    readv(v);
    for (int i = 0; i < n; i++)
    {
        s.insert(abs(v[i] - i - 1));
    }
    if (*s.begin() == 0)
        s.erase(s.begin());
    // for (auto x : s)
    // {
    //     cout << x << " ";
    // }
    // cout << endl;
    ans = *s.begin();
    for (auto x : s)
    {
        ans = __gcd(ans, x);
    }
    cout << ans << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}