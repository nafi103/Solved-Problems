#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define set_bits(x) __builtin_popcount(x)
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 void solve()
{
    int n, x, cnt = 0;
    bool flag = false;
    cin >> n;
    rep(i, 0, n)
    {
        cin >> x;
        if (x == 0)
        {
            cnt++;
        }
        if (x >= 2 && !flag)
        {
            flag = true;
        }
    }
    if (cnt <= (n + 1) >> 1)
    {
        cout << 0 << endl;
    }
    else if (flag | cnt == n)
    {
        cout << 1 << endl;
    }
    else
    {
        cout << 2 << endl;
    }
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}