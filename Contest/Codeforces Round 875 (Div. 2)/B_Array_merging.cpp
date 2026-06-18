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
    int n, x, cnt = 1;
    cin >> n;
    vector<pair<int, int>> arr(2 * n + 1, make_pair(0, 0));
    vector<int> a(n), b(n);
    readv(a);
    readv(b);
    for (int i = 1; i < n; i++)
    {
        if (a[i] != a[i - 1])
        {
            arr[a[i - 1]].first = max(arr[a[i - 1]].first, cnt);
            cnt = 0;
        }
        cnt++;
    }
    arr[a[n - 1]].first = max(arr[a[n - 1]].first, cnt);
    cnt = 1;
    for (int i = 1; i < n; i++)
    {
        if (b[i] == b[i - 1])
            cnt++;
        else
        {
            arr[b[i - 1]].second = max(arr[b[i - 1]].second, cnt);
            cnt = 1;
        }
    }
    arr[b[n - 1]].second = max(arr[b[n - 1]].second, cnt);
    cnt = 1;
    for (int i = 1; i <= 2 * n; i++)
    {
        cnt = max(arr[i].first + arr[i].second, cnt);
    }
    cout << cnt << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}