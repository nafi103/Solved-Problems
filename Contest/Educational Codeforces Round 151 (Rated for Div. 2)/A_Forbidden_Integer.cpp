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
    int n, k, x;
    cin >> n >> k >> x;
    if (x != 1)
    {
        yes;
        cout << n << endl;
        for (int i = 1; i <= n; i++)
            cout << 1 << " ";
        cout << '\n';
    }
    else if ((n & 1 && k == 2) || k == 1)
    {
        no;
    }
    else
    {
        yes;
        cout << n / 2 << endl;
        for (int i = 1; i < n / 2; i++)
            cout << 2 << " ";
        cout << 2 + (n % 2) << endl;
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