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
    vector<ll> v(4);
    readv(v);
    sort(v.begin(), v.end() - 1);
    ll a1 = v[2] - v[1], b1 = v[2] - v[0];
    if (a1 + b1 <= v[3])
    {
        v[3] -= (a1 + b1);
        if (v[3] % 3 == 0)
            yes;
        else
            no;
    }
    else
        no;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}