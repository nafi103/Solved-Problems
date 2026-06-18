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
    int n, m, x, y;
    cin >> n >> m;
    vector<int> v(n + 1, 0), v1;
    for (int i = 0; i < m; i++)
    {
        cin >> x >> y;
        v[y]++;
        v[x]++;
    }
    map<int, int> mp;
    for (int i = 1; i <= n; i++)
    {
        mp[v[i]]++;
    }
    for (auto &x : mp)
    {
        v1.push_back(x.second);
    }
    sort(v1.begin(), v1.end());
    if (v1.size() != 3)
        cout << v1[0] - 1 << " " << v1[1] / (v1[0] - 1) << endl;
    else
        cout << v1[1] << " " << v1[2] / v1[1] << endl;
}
int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}