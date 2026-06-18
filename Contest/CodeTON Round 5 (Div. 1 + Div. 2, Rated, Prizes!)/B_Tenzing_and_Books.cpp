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
#define yes cout << "Yes" << endl
#define no cout << "No" << endl
 void solve()
{
    int n, x, ans = 0, m;
    cin >> n >> x;
    m = ~x;
    vector<int> v(n);
    rep(i, 0, 3)
    {
        readv(v);
        rep(j, 0, n)
        {
            if ((m & v[j]) > 0)
                break;
            ans |= v[j];
        }
    }
    if (ans == x)
        yes;
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