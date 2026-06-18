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
    int n, m;
    cin >> n >> m;
    vector<int> v(n), x(m);
    readv(v);
    readv(x);
    int p1 = 0, p2 = 0;
    while (p1 < n && p2 < m)
    {
        if (v[p1] > x[p2])
        {
            v[p1] -= x[p2];
            p2++;
        }
        else if (v[p1] < x[p2])
        {
            x[p2] -= v[p1];
            p1++;
        }
        else
        {
            p1++;
            p2++;
        }
    }
    if (p1 == n && p2 == m)
        cout << "Draw";
    else if (p1 == n)
        cout << "Tenzing";
    else
        cout << "Tsondu";
    cout << "\n";
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}