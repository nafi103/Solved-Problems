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
    int n, l = 0, r = 0, rem = 0, k = 0;
    string s1, s2;
    cin >> n >> s1 >> s2;
    if (s1 == s2)
    {
        cout << 0 << endl;
        return;
    }
    for (int i = 0; i < n; i++)
    {
        if (s1[i] != s2[i])
            l++;
        if (s1[i] != s2[n - 1 - i])
            r++;
    }
    int ans = min(r, l);
    if(r==l)
    {
        ans = min(2 * r + r % 2 - 1, 2 * l - l % 2);
    }
    else if (ans == r)
    {
        rem = 2;
        ans = 2 * r + r%2 - 1;
    }
    else
    {
        ans = 2 * ans - ans % 2;
    }
    cout << max(ans, rem) << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}