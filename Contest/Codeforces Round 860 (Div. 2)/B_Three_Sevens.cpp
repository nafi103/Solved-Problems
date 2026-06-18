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
    vector<pair<int, int>> v;
    int m, n, x, l;
    cin >> m;
    l = m;
    int arr[m + 1] = {0};
    for (int i = 1; i <= m; i++)
    {
        cin >> n;
        for (int j = 0; j < n; j++)
        {
            cin >> x;
            v.pb(make_pair(x, i));
        }
    }
    sort(all(v));
    int k = v.size();
    for (int i = 1; i < k; i++)
    {
        if (v[i].first != v[i - 1].first)
        {
            if (arr[v[i - 1].second] == 0)
            {
                m--;
                arr[v[i - 1].second] = v[i - 1].first;
            }
            if (!m)
                break;
        }
    }
    if (arr[v[k - 1].second] == 0)
    {
        arr[v[k - 1].second] = v[k - 1].first;
        m--;
    }
    if (m)
    {
        cout << -1 << endl;
        return;
    }
    for (int i = 1; i <= l; i++)
    {
        cout << arr[i] << " ";
    }
    cout << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}