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
 void solve()
{
    ll n, m;
    cin >> n >> m;
    if (n > m && n % 3 == 0)
    {
        queue<ll> q;
        set<ll> s;
        bool flag = false;
        ll fi = n / 3;
        ll se = fi * 2;
        if (fi % 3 == 0)
        {
            q.push(fi);
            s.insert(fi);
        }
        if (se % 3 == 0)
        {
            q.push(se);
            s.insert(se);
        }
        if (fi == m || se == m)
        {
            flag = 1;
        }
        while (!q.empty())
        {
            ll nu = q.front();
            fi = nu / 3;
            se = fi * 2;
            if (fi % 3 == 0 && s.find(fi) == s.end())
                q.push(fi);
            if (se % 3 == 0 && s.find(fi) == s.end())
                q.push(se);
            if (fi == m || se == m)
            {
                flag = 1;
                break;
            }
            q.pop();
        }
        if (flag)
        {
            cout << "YES" << endl;
        }
        else
        {
            cout << "NO" << endl;
        }
    }
    else
    {
        if (m == n)
            yes;
        else
        {
            no;
        }
    }
}
 int main()
{
    fastIO;
    ll t;
    cin >> t;
    while (t--)
        solve();
}