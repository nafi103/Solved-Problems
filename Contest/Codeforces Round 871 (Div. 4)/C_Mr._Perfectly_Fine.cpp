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
    ll n, s1 = INT_MAX, s2 = INT_MAX, s3 = INT_MAX, m;
    string str;
    bool one = false, two = false, three = false;
    cin >> n;
    for (int i = 0; i < n; i++)
    {
        cin >> m >> str;
        if (str == "11")
        {
            three = true;
            s3 = min(s3, m);
        }
        if (str == "01")
        {
            one = true;
            s1 = min(s1, m);
        }
        if (str == "10")
        {
            two = true;
            s2 = min(s2, m);
        }
    }
    if ((one && two) || three)
    {
        cout << min(s3, s1 + s2) << endl;
    }
    else
        cout << -1 << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}