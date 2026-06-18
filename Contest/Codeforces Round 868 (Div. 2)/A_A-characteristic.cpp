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
    int n, k, x = -1;
    cin >> n >> k;
    for (int i = 0; i < n; i++)
    {
        if ((i * (i - 1) / 2) + ((n - i) * (n - i - 1) / 2) == k)
        {
            x = i;
            break;
        }
    }
    if (x == -1)
        no;
    else
    {
        yes;
        int k = n - x;
        while (k--)
            cout << 1 << " ";
        while (x--)
            cout << -1 << " ";
        cout << endl;
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