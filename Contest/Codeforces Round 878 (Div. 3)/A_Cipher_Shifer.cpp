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
    int n, cnt = 0;
    string ans = "";
    char x;
    cin >> n >> x;
    ans.pb(x);
    for (int i = 1; i < n; i++)
    {
        cin >> x;
        if (x == ans[cnt] && i + 1 < n)
        {
            cin >> x;
            ans.pb(x);
            cnt++;
            i++;
        }
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