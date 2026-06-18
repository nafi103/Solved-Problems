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
    int n, k, x;
    cin >> n >> k;
    vector<pair<ll, ll>> v1;
    for (int i = 0; i < n; i++)
    {
        cin >> x;
        v1.pb(make_pair(x, i));
    }
    vector<ll> v2(n);
    readv(v2);
    sort(v1.begin(), v1.end());
    sort(all(v2));
    ll arr[n];
    for (int i = 0; i < n; i++)
    {
        arr[v1[i].second] = v2[i];
    }
    for (int i = 0; i < n; i++)
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