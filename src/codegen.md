
        # Codegen
        
<style>
    .tabs {
        display: grid;
        grid-template-columns: repeat(3, minmax(200px, 1fr));
        grid-template-rows: auto 1fr;
        column-gap: 1rem;
    }
    
    .tabs details {
        display: grid;
        grid-column: 1 / -1;
        grid-row: 1 / span 2;
        grid-template-columns: subgrid;
        grid-template-rows: subgrid;
    }
    
    .tabs summary {
        grid-column: var(--n) / span 1;
        grid-row: 1;
        display: grid;
        padding: 1rem;
        border-bottom: 2px solid dodgerblue;
        cursor: pointer;
        z-index: 1;
    }
    
    .tabs details[open] :is(summary, .summary) {
        font-weight: bold;
    }
    
    .tabs details::details-content {
        grid-row: 2;
        grid-column: 1 / -1;
        padding: 1rem;
        border-bottom: 2px solid dodgerblue;
    }
    
    .tabs details:not([open])::details-content {
        display: none;
    }
    
    @media screen and (width < 40em) {
        .tabs {
            grid-template-columns: repeat(3, minmax(100px, 1fr));
            column-gap: .5rem;
        }
    
        .tabs summary,
        .tabs details::details-content {
            padding: .5rem;
        }
    }
</style>
        
<div class="tabs">
    <details name="tab" style="--n: 1" open>
    <summary>Source</summary>
    <div>
        <p>Your recent tracks:</p>
        <ul>
        <li>The Beths - Mother, Pray For Me</li>
        <li>The Beths - Metal</li>
        <li>The Beths - No Joy</li>
        <li>The Beths - Mosquitoes</li>
        <li>The Beths - Straight Line Was A Lie</li>
        </ul>
    </div>
    </details>
    <details name="tab" style="--n: 2">
    <summary>Loved tracks</summary>
    <div>
        <p>Tracks you loved:</p>
        <ul>
        <li>Marnie Stern - Believing Is Seeing</li>
        <li>FKA twigs - Girl Feels Good</li>
        <li>Fat Dog - Running</li>
        <li>Parquet Courts - Tenderness</li>
        <li>Sufjan Stevens - Will Anybody Ever Love Me?</li>
        </ul>
    </div>
    </details>
    <details name="tab" style="--n: 3">
    <summary>Following</summary>
    <div>
        <p>Artists you follow:</p>
        <ul>
        <li>Amyl and the Sniffers</li>
        <li>Du Blonde</li>
        <li>Magdalena Bay</li>
        <li>Flying Lotus</li>
        <li>Horsegirl</li>
        </ul>
    </div>
    </details>
</div>