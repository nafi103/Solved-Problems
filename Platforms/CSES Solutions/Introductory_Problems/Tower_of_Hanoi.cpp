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
#define endl '\n'
#define yes cout << "YES" << endl
#define no cout << "NO" << endl

void solve(ll n, ll ft, ll tt, ll at)
{
    if (n == 1)
    {
        cout << ft << " " << tt << endl;
    }
    else
    {
        solve(n - 1, ft, at, tt);
        cout << ft << " " << tt << endl;
        solve(n - 1, at, tt, ft);
    }
}

int main()
{
    fastIO;
    ll t;
    cin >> t;
    cout << pow(2, t) - 1 << endl;
    solve(t, 1, 3, 2);
}